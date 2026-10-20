"""Translation stages, measurements, and archive recovery; no benchmark suite runs."""

import copy
import csv
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))
from evaluation import campaign as audit, translation as runner


class TranslationRunnerTests(unittest.TestCase):
    def test_stage_status_uses_process_result_without_solver_answers(self):
        cases = [(0, None, "", False, "passed"),
                 (0, "wall_timeout", "", False, "timeout"),
                 (1, "memory_limit", "", False, "memory_limit"),
                 (1, None, "cvc5.Error.unsupported: feature", True, "unsupported"),
                 (1, None, "cvc5.Error.unsupported: feature", False, "error"),
                 (1, None, "syntax error", True, "error"),
                 (None, "launch_error", "", False, "launch_error")]
        for code, reason, diagnostic, translation, expected in cases:
            with self.subTest(code=code, reason=reason, translation=translation):
                result = dict(returncode=code, limit_reason=reason, diagnostic=diagnostic,
                              answers=[])
                self.assertEqual(runner.stage_status(result, translation), expected)

    def test_summary_populations_and_stage_timings(self):
        good = dict(outcome="passed", metrics_status="passed", control=False,
                    sha256="good", source_path="good.smt2", generated="good.lean",
                    token_ratio=2, code_loc_ratio=3, byte_ratio=4, input_tokens=10,
                    output_tokens=20, input_code_loc=2, output_code_loc=6)
        for stage in ("translation", "statements", "template"):
            good.update({stage + "_status": "passed", stage + "_seconds": 1})
        metric_failure = dict(good, sha256="metrics", metrics_status="error", output_tokens=999)
        type_failure = dict(good, sha256="type", outcome="statements_error",
                            statements_status="error", statements_seconds=999, output_tokens=999)
        translation_failure = dict(good, sha256="translation", outcome="translation_timeout",
                                   translation_status="timeout", translation_seconds=999,
                                   statements_status="not_run", template_status="not_run",
                                   metrics_status="not_run")
        rows = [good, metric_failure, type_failure, translation_failure]
        for row in rows:
            row["stages"] = {
                stage: dict(status=row[stage + "_status"], seconds=row[stage + "_seconds"])
                for stage in ("translation", "statements", "template")
                if row[stage + "_status"] != "not_run"
            }
        summary = runner.summarize(rows)
        self.assertEqual(summary["completed"], 4)
        self.assertEqual(summary["passed"], 2)
        self.assertEqual(summary["metrics_errors"], 1)
        self.assertEqual(summary["size_metrics_passed_inputs"], 1)
        self.assertEqual(summary["output_tokens"]["total"], 20)
        self.assertEqual(summary["output_code_loc"]["total"], 6)
        self.assertEqual([r["source_path"] for r in summary["largest_expansions"]], ["good.smt2"])
        for stage, count in (("translation", 3), ("statements", 2), ("template", 3)):
            self.assertEqual(summary[stage + "_successful_seconds"]["count"], count)
            self.assertEqual(summary[stage + "_successful_seconds"]["maximum"], 1)

    def test_native_lean_rejects_statement_sorry_but_accepts_template(self):
        prefix = subprocess.check_output(["lean", "--print-prefix"], text=True).strip()
        lean = str(Path(prefix) / "bin/lean")
        runner.processes.STOP.clear()
        try:
            with tempfile.TemporaryDirectory() as directory:
                out = Path(directory)
                source = out / "Admitted.lean"
                source.write_text("import Init\ntheorem admitted : True := by sorry\n")
                case = dict(archive="synthetic", archive_member="admitted.smt2")
                args = SimpleNamespace(timeout=10)
                statement = runner.run_stage([lean, "-j1", "--error=hasSorry", str(source)],
                                             "statements", case, args, out)
                template = runner.run_stage([lean, "-j1", str(source)],
                                            "template", case, args, out)
                self.assertEqual(statement["status"], "error", statement)
                self.assertEqual(template["status"], "passed", template)
                self.assertEqual(template["sorry_warnings"], 1)
                self.assertEqual(template["warning_count"], 1)
                self.assertFalse(runner.processes.ACTIVE)
        finally:
            runner.processes.STOP.clear()


def record(name, input_tokens, output_tokens, outcome="passed", sha256=None):
    value = dict(
        outcome=outcome, metrics_status="passed", input_metrics_status="passed",
        control=False, sha256=sha256 or name, source_path=name + ".smt2",
        generated=name + ".lean", input_tokens=input_tokens, output_tokens=output_tokens,
        input_code_loc=1, output_code_loc=2, input_bytes=input_tokens,
        output_bytes=output_tokens, output_statement_bytes=output_tokens,
        token_ratio=output_tokens / input_tokens, code_loc_ratio=2,
        byte_ratio=output_tokens / input_tokens, statement_byte_ratio=output_tokens / input_tokens,
        stages={}, translation_and_statements_seconds=3,
    )
    for index, stage in enumerate(("translation", "statements", "template"), 1):
        status = "error" if outcome == stage + "_error" else "passed"
        value.update({stage + "_status": status, stage + "_seconds": index})
        value["stages"][stage] = dict(status=status, seconds=index, sampled_peak_rss_kb=128)
    return value


class BookkeepingTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("cloc"), "cloc is not installed")
    def test_failed_translation_retains_exact_input_measurements(self):
        text = b"; a comment\r\n(assert true)\r\n(check-sat)\r\n"
        with tempfile.TemporaryDirectory() as directory:
            out = Path(directory)
            source = out / "source.smt2"
            source.write_bytes(text)
            case = dict(path=str(source))
            stage = dict(status="unsupported", seconds=1.25, limit_reason=None,
                         diagnostic="cvc5.Error.unsupported: fixture")
            failed = dict(artifacts="case", outcome="translation_unsupported",
                          translation_status="unsupported", statements_status="not_run",
                          template_status="not_run", metrics_status="not_run",
                          stages={"translation": stage}, input_bytes=len(text))
            with patch.object(runner, "_check_case", return_value=failed):
                result = runner.check_case(case, SimpleNamespace(cloc=shutil.which("cloc")),
                                           out, out / "generated", out / "lean")
            self.assertEqual(result["outcome"], "translation_unsupported")
            self.assertEqual(result["input_metrics_status"], "passed")
            self.assertEqual(result["metrics_status"], "not_run")
            self.assertEqual(result["input_bytes"], len(text))
            self.assertEqual(result["input_code_loc"], 2)
            self.assertEqual(result["input_tokens"], 7)
            self.assertEqual(result["input_structure"]["max_parenthesis_depth"], 1)
            self.assertEqual(result["failed_stage"], "translation")
            self.assertEqual(result["failure_category"], "unsupported")
            self.assertEqual(result["measured_stage_seconds"], 1.25)
            self.assertNotIn("translation_and_statements_seconds", result)
            self.assertTrue((out / "case/input-metrics/cloc.json").is_file())

    def test_resource_categories_and_external_limit_precedence(self):
        for diagnostic, expected in (
            ("excessive memory consumption", "memory_limit"),
            ("maximum recursion depth has been reached", "recursion_limit"),
            ("maximum number of heartbeats has been reached", "heartbeat_limit"),
            ("expected at least one check-sat command", "missing_check_sat"),
            ("ordinary elaboration failure", "error"),
        ):
            with self.subTest(diagnostic=diagnostic):
                stage = dict(status="error", limit_reason=None, diagnostic=diagnostic)
                self.assertEqual(runner.failure_category(stage), expected)
                stage["limit_reason"] = "wall_timeout"
                self.assertEqual(runner.failure_category(stage), "wall_timeout")

    def test_summary_ratio_of_totals_and_distinct_content_outcomes(self):
        small = record("small", 10, 100, sha256="duplicate")
        large = record("large", 100, 100)
        failed = record("failed", 10, 10000, outcome="statements_error", sha256="duplicate")
        summary = runner.summarize([small, large, failed])
        self.assertEqual(summary["completed"], 3)
        self.assertEqual(summary["passed"], 2)
        self.assertEqual(summary["size_metrics_passed_inputs"], 2)
        self.assertEqual(summary["token_ratio"]["median"], 5.5)
        self.assertAlmostEqual(summary["total_token_ratio"], 200 / 110)
        self.assertEqual(summary["output_tokens"]["total"], 200)
        self.assertEqual(summary["input_size_all_attempted"]["input_tokens"]["count"], 3)
        self.assertEqual(summary["distinct_contents"], 2)
        self.assertEqual(summary["distinct_content_outcomes"], {"mixed": 1, "passed": 1})
        self.assertEqual(summary["statements_failed_attempt_seconds_total"], 2)
        self.assertEqual(summary["statements_all_attempt_seconds"]["count"], 3)
        self.assertEqual(summary["translation_and_statements_seconds"]["count"], 2)
        self.assertEqual(summary["statements_successful_seconds"]["count"], 2)


class ResumeArchiveTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()
        self.directory = self.root / "archive"
        self.directory.mkdir()
        self.generated = self.root / "generated"
        self.generated.mkdir()
        self.attempt = self.directory / "attempts" / "resume-test"
        self.attempt.mkdir(parents=True)
        self.args = SimpleNamespace(generated=self.generated, memory_mb=4096)
        self.cases = []
        for name in ("retained", "missing"):
            source = self.root / (name + ".smt2")
            source.write_text("(assert true)\n(check-sat)\n")
            self.cases.append(dict(archive="archive.tar.gz", archive_member=source.name,
                path=str(source), source_path=source.name, suite="fixture", logic="ALL",
                sha256=audit.digest(source), bytes=str(source.stat().st_size),
                output_relative=name + ".lean"))
        self.retained = self.failed_translation(self.cases[0], self.directory)
        self.original_line = json.dumps(self.retained) + "\n"
        (self.directory / "results.jsonl").write_text(self.original_line)
        runner.processes.STOP.clear()
        self.addCleanup(runner.processes.STOP.clear)

    def failed_translation(self, case, out):
        log = out / (case["archive_member"] + ".log")
        log.write_text("timeout diagnostic\n")
        stage = dict(status="timeout", limit_reason="wall_timeout",
                     failure_category="wall_timeout", failure=None,
                     returncode=-15, seconds=300, stdout=log.name, stderr=log.name)
        return dict(case, artifacts="cases/" + case["archive_member"], stages={"translation": stage},
            query_count=1, input_metrics_status="passed", metrics_status="not_run", control=False,
            outcome="translation_timeout", translation_status="timeout",
            translation_seconds=300, statements_status="not_run", template_status="not_run",
            failure_category="wall_timeout")

    def run_worker(self, check_case):
        records, expected, seen = runner.read_records(
            self.directory, self.cases, self.generated, runner, audit)
        with patch.object(runner, "check_case", side_effect=check_case) as check, \
                patch.object(runner.processes, "sample_memory"):
            code = runner.run_archive(self.directory, self.attempt, self.args, self.cases,
                                      records, expected, seen, runner, audit, Path("/unused/lean"))
        return code, check, records

    def test_retains_expected_failure_and_runs_only_missing_case_with_rebased_logs(self):
        def check_case(case, args, out, generated, lean):
            self.assertEqual(out, self.attempt)
            self.assertEqual(generated, self.generated)
            return self.failed_translation(case, out)
        code, check, records = self.run_worker(check_case)
        self.assertEqual(code, 0)
        check.assert_called_once()
        self.assertEqual(check.call_args.args[0], self.cases[1])
        data = (self.directory / "results.jsonl").read_text()
        self.assertTrue(data.startswith(self.original_line))
        self.assertEqual(records[0], self.retained)
        prefix = "attempts/resume-test/"
        self.assertTrue(records[1]["artifacts"].startswith(prefix))
        for channel in ("stdout", "stderr"):
            self.assertTrue(records[1]["stages"]["translation"][channel].startswith(prefix))
        progress = json.loads((self.directory / "progress.json").read_text())
        self.assertEqual((progress["state"], progress["completed"], progress["total"]),
                         ("complete", 2, 2))
        self.assertTrue(progress["complete_archive"])
        self.assertEqual(json.loads((self.directory / "summary.json").read_text()),
                         runner.summarize(records))
        with (self.directory / "results.csv").open(newline="") as stream:
            self.assertEqual(len(list(csv.DictReader(stream))), 2)
        self.assertFalse((self.directory / "failure.json").exists())

    def test_duplicate_truncated_and_manifest_mismatch_records_are_rejected(self):
        altered = dict(self.retained, output_relative="changed.lean")
        for data, message in ((self.original_line * 2, "Duplicate"),
                              (self.original_line.rstrip(), "truncated"),
                              (json.dumps(altered) + "\n", "manifest mismatch")):
            with self.subTest(message=message):
                (self.directory / "results.jsonl").write_text(data)
                with self.assertRaisesRegex(RuntimeError, message):
                    runner.read_records(self.directory, self.cases, self.generated, runner, audit)

    def test_interruption_is_saved_but_never_marked_complete(self):
        def interrupted(case, args, out, generated, lean):
            row = self.failed_translation(case, out)
            runner.processes.STOP.set()
            row["input_metrics_status"] = "not_run"
            return row
        code, _, records = self.run_worker(interrupted)
        self.assertEqual(code, 1)
        self.assertEqual(len(records), 2)
        self.assertEqual(json.loads((self.directory / "progress.json").read_text())["state"],
                         "interrupted")
        self.assertTrue((self.directory / "failure.json").is_file())
        with self.assertRaisesRegex(RuntimeError, "Input metrics"):
            runner.read_records(self.directory, self.cases, self.generated, runner, audit)

    def test_exception_is_recorded_for_later_reconciliation(self):
        code, _, records = self.run_worker(RuntimeError("fixture failure"))
        self.assertEqual(code, 1)
        self.assertEqual(records[-1]["outcome"], "runner_error")
        self.assertIn("fixture failure", records[-1]["reason"])
        self.assertEqual(len((self.directory / "results.jsonl").read_text().splitlines()), 2)
        self.assertTrue((self.directory / "failure.json").is_file())

    def test_unreconciled_generated_file_cannot_be_overwritten(self):
        output = self.generated / self.cases[1]["output_relative"]
        output.write_text("must survive")
        code, check, records = self.run_worker(AssertionError("must not run"))
        self.assertEqual(code, 1)
        check.assert_not_called()
        self.assertEqual(len(records), 1)
        self.assertEqual(output.read_text(), "must survive")

    def test_rebase_rejects_escaping_log_paths(self):
        row = copy.deepcopy(self.retained)
        row["stages"]["translation"]["stdout"] = "../old.log"
        with self.assertRaisesRegex(ValueError, "Unsafe"):
            runner.rebase_record(row, self.attempt, self.directory, runner)


if __name__ == "__main__":
    unittest.main()
