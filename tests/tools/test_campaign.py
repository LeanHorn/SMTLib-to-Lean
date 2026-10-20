"""Campaign guards, record audits, recovery, and frozen modules without evaluations."""

import copy
import json
import os
from pathlib import Path
import sys
import tempfile
import time
from types import ModuleType, SimpleNamespace
import unittest
from unittest.mock import Mock, patch

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))
from evaluation import campaign
from evaluation import translation as runner
from evaluation.campaign import partition_records, read_rows, write_rows


class CampaignGuardTests(unittest.TestCase):
    def test_guard_requires_both_owned_assertions_and_ac(self):
        evidence = """PreventUserIdleSystemSleep 1
PreventSystemSleep 1
 pid 123(caffeinate): [0x1] 00:00:00 PreventUserIdleSystemSleep named: "caffeinate"
 pid 123(caffeinate): [0x2] 00:00:00 PreventSystemSleep named: "caffeinate"
"""
        battery = "Now drawing from 'AC Power'"
        self.assertEqual(campaign.assertion_evidence(evidence, battery, 123)["pid"], 123)
        for assertions, power, pid in (
                (evidence, battery, 456), (evidence, "Now drawing from 'Battery Power'", 123),
                (evidence.replace("PreventSystemSleep 1", "PreventSystemSleep 0"), battery, 123),
                (evidence.replace("pid 123(caffeinate): [0x2]", "pid 456(caffeinate): [0x2]"),
                 battery, 123)):
            with self.assertRaises(RuntimeError):
                campaign.assertion_evidence(assertions, power, pid)

    def test_orphan_detection_does_not_adopt_unrelated_processes(self):
        instance = campaign.Campaign(SimpleNamespace(out=Path("/private/tmp/campaign"),
                                                     generated=Path("/private/tmp/generated")))
        instance.translator, instance.lean = Path("/private/tmp/campaign/snapshot/smt2lean"), Path("/lean")
        instance.child = SimpleNamespace(pid=100, returncode=1)
        header = " 1 200 " + str(os.getuid()) + " Tue Oct 20 01:02:03 2026 S "
        table = ("200" + header + str(instance.translator) + " input --out /private/tmp/campaign/archives/a\n"
                 "201" + header + "/unrelated --out /private/tmp/campaign/archives/a\n"
                 "202" + header + str(instance.translator) + " input --out /another/campaign\n")
        with patch.object(campaign, "output", return_value=table):
            instance.capture_owned()
        self.assertEqual(set(instance.owned), {200})
        with patch.object(campaign, "output", return_value=""):
            instance.capture_owned()
        self.assertFalse(instance.owned)

    def test_suspected_sleep_stops_before_more_work(self):
        instance = campaign.Campaign(SimpleNamespace(out=Path("/unused")))
        instance.last_clock = (100, 100)
        with patch.object(campaign.time, "time", return_value=150), \
                patch.object(campaign.time, "monotonic", return_value=110):
            with self.assertRaisesRegex(RuntimeError, "suspend or clock change"):
                instance.checkpoint()


class CampaignRecordTests(unittest.TestCase):
    def fixture(self, root, status="passed"):
        source, generated = root / "input.smt2", root / "generated"
        source.write_text("(assert true)\n(check-sat)\n")
        generated.mkdir()
        manifest = dict(archive="archive", archive_member="input.smt2",
                        bytes=str(source.stat().st_size), sha256=campaign.digest(source))
        row = dict(manifest, path=str(source), query_count=1, input_metrics_status="passed",
                   metrics_status="not_run", stages={}, outcome="translation_" + status,
                   translation_status=status, statements_status="not_run", template_status="not_run")
        def stage(name, state):
            log = root / (name + ".log")
            log.write_text("")
            row["stages"][name] = dict(status=state, limit_reason="wall_timeout" if state == "timeout" else None,
                failure_category="wall_timeout" if state == "timeout" else None,
                failure=None, returncode=0 if state == "passed" else 1, seconds=1,
                stdout=log.name, stderr=log.name)
            row[name + "_status"], row[name + "_seconds"] = state, 1
        stage("translation", status)
        if status == "passed":
            output = generated / "input.lean"
            output.write_text("def Problem : Prop := True\n")
            row.update(generated=str(output), output_relative="input.lean", emitted_queries=1,
                       output_bytes=output.stat().st_size, output_sha256=campaign.digest(output),
                       metrics_status="passed", outcome="passed")
            stage("statements", "passed")
            stage("template", "passed")
        expected = {("archive", "input.smt2"): manifest}
        return row, expected, generated

    def test_expected_failed_translation_is_retained(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name).resolve()
            row, expected, generated = self.fixture(root, "timeout")
            self.assertEqual(campaign.validate_record(row, expected, generated, runner, root),
                             ("archive", "input.smt2"))

    def test_completed_translation_is_auditable(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name).resolve()
            row, expected, generated = self.fixture(root)
            self.assertEqual(campaign.validate_record(row, expected, generated, runner, root),
                             ("archive", "input.smt2"))

    def test_measurement_and_infrastructure_failures_stop(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name).resolve()
            row, expected, generated = self.fixture(root)
            edits = [
                {"input_metrics_status": "error"}, {"metrics_status": "error"},
                {"emitted_queries": 0}, {"outcome": "output_inspection_error"},
                {"translation_status": "launch_error"}, {"query_count": -1},
                {"output_sha256": "changed"}, {"sha256": "changed"},
            ]
            for edit in edits:
                with self.subTest(edit=edit), self.assertRaises(RuntimeError):
                    campaign.validate_record(dict(row, **edit), expected, generated, runner, root)
            broken = copy.deepcopy(row)
            broken["stages"]["translation"]["failure"] = "cannot capture output"
            with self.assertRaises(RuntimeError):
                campaign.validate_record(broken, expected, generated, runner, root)

    def test_query_mismatch_cannot_hide_behind_benchmark_error(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name).resolve()
            row, expected, generated = self.fixture(root)
            row.update(emitted_queries=2, statements_status="error", outcome="statements_error")
            row["stages"]["statements"].update(status="error", returncode=1, failure_category="heartbeat_limit")
            with self.assertRaisesRegex(RuntimeError, "Query-count"):
                campaign.validate_record(row, expected, generated, runner, root)

    def test_unclassified_errors_need_review(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name).resolve()
            row, expected, generated = self.fixture(root, "error")
            row["stages"]["translation"]["failure_category"] = "error"
            with self.assertRaisesRegex(RuntimeError, "Unclassified"):
                campaign.validate_record(row, expected, generated, runner, root)

    def test_source_and_generated_drift_stop(self):
        for target in ("path", "generated"):
            with self.subTest(target=target), tempfile.TemporaryDirectory() as name:
                root = Path(name).resolve()
                row, expected, generated = self.fixture(root)
                Path(row[target]).write_text("changed")
                with self.assertRaises(RuntimeError):
                    campaign.validate_record(row, expected, generated, runner, root)

    def test_final_truncated_record_stops(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name).resolve()
            (root / "results.jsonl").write_text(json.dumps({"incomplete": True}))
            instance = campaign.Campaign(SimpleNamespace(out=root))
            with self.assertRaisesRegex(RuntimeError, "Truncated"):
                instance.inspect(root, root, [], final=True)


class ResumeCampaignTests(unittest.TestCase):
    def row(self, name, status):
        return dict(archive="suite", archive_member=name, outcome=status,
                    stages={"translation": {"status": status}})

    def test_keeps_resource_failures_and_retries_only_interruption(self):
        rows = [self.row("a", "passed"), self.row("b", "memory_limit"),
                self.row("c", "interrupted")]
        kept, retry = partition_records(rows)
        self.assertEqual(kept, rows[:2])
        self.assertEqual(retry, rows[2:])

    def test_duplicate_or_nonfinal_interruption_requires_review(self):
        for rows in ([self.row("a", "passed")] * 2,
                     [self.row("a", "interrupted"), self.row("b", "passed")]):
            with self.assertRaises(RuntimeError):
                partition_records(rows)

    def test_roundtrip_and_truncated_record(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "results.jsonl"
            rows = [self.row("a", "passed")]
            write_rows(path, rows)
            self.assertEqual(read_rows(path), rows)
            path.write_bytes(path.read_bytes().rstrip(b"\n"))
            with self.assertRaisesRegex(RuntimeError, "Truncated"):
                read_rows(path)

    def test_new_and_legacy_resume_load_the_saved_environment_and_base(self):
        original_cwd = Path.cwd()
        try:
            for legacy in (False, True):
                with self.subTest(legacy=legacy), tempfile.TemporaryDirectory() as directory:
                    root = Path(directory).resolve()
                    out = root / "run"
                    snapshot = out / "snapshot"
                    snapshot.mkdir(parents=True)
                    names = (("evaluate_translation.py", "evaluation_metrics.py", "evaluate_solvers.py",
                              "evaluation_campaign.py") if legacy else
                             (*campaign.RUNNERS, "campaign.py"))
                    for name in names[:-1]:
                        (snapshot / name).write_text("FROZEN = True\n")
                    (snapshot / names[-1]).write_text(
                        "from pathlib import Path\nimport os\n"
                        "ROOT = Path(os.environ['SMT2LEAN_PROJECT_ROOT'])\n"
                        "SCHEDULE = [('saved.tar.gz', 2)]\n"
                        "class Campaign:\n"
                        "    def __init__(self, args):\n"
                        "        self.args = args\n")
                    metadata = dict(root=str(root), environment={
                        "SMT2LEAN_PROJECT_ROOT": str(root), "CAMPAIGN_TEST_VALUE": "saved",
                        "CAMPAIGN_TEST_REMOVE": None},
                        arguments=dict(out=str(out), generated=str(root / "generated"),
                                       translator=str(root / "translator")),
                        pins={str(path): campaign.digest(path) for path in snapshot.iterdir()})
                    (out / "metadata.json").write_text(json.dumps(metadata))
                    with patch.dict(os.environ, {"CAMPAIGN_TEST_VALUE": "live",
                                                 "CAMPAIGN_TEST_REMOVE": "remove"}), \
                            patch.dict(sys.modules), patch.object(sys, "path", list(sys.path)):
                        resumed, schedule = campaign.load_resume(out)
                        self.assertEqual(schedule, [("saved.tar.gz", 2)])
                        self.assertEqual(resumed.args.out, out)
                        self.assertEqual(os.environ["CAMPAIGN_TEST_VALUE"], "saved")
                        self.assertNotIn("CAMPAIGN_TEST_REMOVE", os.environ)
                        base = type(resumed).__bases__[0]
                        self.assertEqual(Path(sys.modules[base.__module__].__file__),
                                         snapshot / names[-1])
                    os.chdir(original_cwd)
        finally:
            os.chdir(original_cwd)

    def test_resumed_worker_gets_startup_grace_for_the_previous_progress_file(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            progress = root / "progress.json"
            progress.write_text("{}")
            os.utime(progress, (time.time() - 300, time.time() - 300))
            instance = campaign.Campaign(SimpleNamespace(out=root, generated=root))
            instance.current = {}
            for name in ("capture_owned", "checkpoint", "inspect", "progress"):
                setattr(instance, name, Mock())
            child = Mock(pid=123, returncode=0)
            child.poll.side_effect = [None, 0]
            with patch.object(campaign.subprocess, "Popen", return_value=child), \
                    patch.object(campaign.time, "monotonic", side_effect=[100, 101]):
                instance.supervise_archive(root, root, [], ["worker"], root / "worker.log",
                                           resuming=True)
            instance.progress.assert_called_once_with("running")
            child.poll.side_effect = [None]
            with patch.object(campaign.subprocess, "Popen", return_value=child):
                with self.assertRaisesRegex(RuntimeError, "heartbeat"):
                    instance.supervise_archive(root, root, [], ["worker"], root / "fresh.log")


class FrozenCampaignTests(unittest.TestCase):
    def test_frozen_import_replaces_live_flat_modules(self):
        with tempfile.TemporaryDirectory() as directory:
            snapshot = Path(directory).resolve()
            helper = snapshot / "frozen_helper.py"
            runner = snapshot / "frozen_runner.py"
            helper.write_text("VALUE = 'snapshot'\n")
            runner.write_text("import frozen_helper\nVALUE = frozen_helper.VALUE\n")
            live = ModuleType("frozen_helper")
            live.__file__ = "/other/frozen_helper.py"
            live.VALUE = "live"
            pins = {str(path): campaign.digest(path) for path in (runner, helper)}
            with patch.dict(sys.modules, {"frozen_helper": live}), patch.object(sys, "path", list(sys.path)):
                modules = campaign.import_frozen(snapshot, (runner.name, helper.name), pins)
                self.assertEqual(modules["frozen_runner"].VALUE, "snapshot")
                self.assertEqual(Path(modules["frozen_helper"].__file__), helper)

    def test_tampered_snapshot_is_rejected_before_import_or_cache_changes(self):
        with tempfile.TemporaryDirectory() as directory:
            snapshot = Path(directory).resolve()
            worker = snapshot / "frozen_worker.py"
            worker.write_text("VALUE = 'original'\n")
            pins = {str(worker): campaign.digest(worker)}
            worker.write_text("raise AssertionError('Must not execute')\n")
            live = ModuleType("frozen_worker")
            live.__file__ = "/other/frozen_worker.py"
            with patch.dict(sys.modules, {"frozen_worker": live}):
                with self.assertRaisesRegex(RuntimeError, "Pinned runner changed"):
                    campaign.import_frozen(snapshot, (worker.name,), pins)
                self.assertIs(sys.modules["frozen_worker"], live)


if __name__ == "__main__":
    unittest.main()
