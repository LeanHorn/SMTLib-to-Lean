"""Small runner checks using synthetic records and a single admitted Lean theorem."""

from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))
import evaluate_translation as runner


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
        summary = runner.summarize([good, metric_failure, type_failure, translation_failure])
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


if __name__ == "__main__":
    unittest.main()
