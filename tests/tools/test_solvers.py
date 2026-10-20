"""Solver process cleanup and corpus loading using small synthetic fixtures."""

import csv
import io
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tarfile
import tempfile
import time
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))
from evaluation import solvers as runner


class CleanupTests(unittest.TestCase):
    def setUp(self):
        runner.STOP.clear()
        self.temp = tempfile.TemporaryDirectory()
        self.out = Path(self.temp.name)

    def tearDown(self):
        self.assertFalse(runner.ACTIVE)
        runner.STOP.clear()
        self.temp.cleanup()

    def run_process(self, code, timeout=0.2):
        case = dict(archive="test", archive_member="test.smt2", path="test.smt2")
        args = SimpleNamespace(timeout=timeout, log_mb=1)
        return runner.run_one(case, "test", [sys.executable, "-c", code], args, self.out)

    def assert_gone(self, pid):
        result = subprocess.run(["ps", "-p", str(pid), "-o", "stat="],
                                capture_output=True, text=True, timeout=2)
        self.assertTrue(not result.stdout.strip() or result.stdout.strip().startswith("Z"))

    def test_forced_wall_timeout(self):
        result = self.run_process("import time; time.sleep(30)")
        self.assertEqual(result["status"], "timeout")
        self.assertEqual(result["timeout_method"], "wall_timeout")
        self.assertLess(result["seconds"], 3)
        self.assert_gone(result["pid"])

    def test_denied_group_signal_falls_back_to_owned_pids(self):
        code = ("import subprocess,sys,time; "
                "p=subprocess.Popen([sys.executable,'-c','import time; time.sleep(30)']); "
                "print(p.pid,flush=True); time.sleep(30)")
        with patch.object(runner.os, "killpg", side_effect=PermissionError(1, "denied")):
            result = self.run_process(code)
        self.assertEqual(result["status"], "timeout")
        self.assertIsNone(result["failure"])
        self.assertFalse(runner.STOP.is_set())
        self.assert_gone(result["pid"])
        self.assert_gone(int((self.out / result["stdout"]).read_text()))

    def test_exited_parent_does_not_leave_descendant_or_pipe_reader(self):
        code = ("import subprocess,sys; "
                "p=subprocess.Popen([sys.executable,'-c','import time; time.sleep(30)']); "
                "print(p.pid,file=sys.stderr,flush=True); print('sat',flush=True)")
        with patch.object(runner.os, "killpg", side_effect=PermissionError(1, "denied")):
            result = self.run_process(code, timeout=2)
        self.assertEqual(result["status"], "sat")
        self.assert_gone(int((self.out / result["stderr"]).read_text()))

    def test_failed_termination_is_bounded_and_excluded(self):
        real_killpg = os.killpg
        start = time.monotonic()
        with patch.object(runner.os, "killpg", side_effect=PermissionError(1, "denied")), \
             patch.object(runner.os, "kill", side_effect=PermissionError(1, "denied")):
            result = self.run_process("import time; time.sleep(30)")
        try:
            self.assertEqual(result["status"], "error")
            self.assertEqual(result["limit_reason"], "cleanup_error")
            self.assertTrue(runner.STOP.is_set())
            self.assertLess(time.monotonic() - start, 8)
        finally:
            real_killpg(result["pid"], signal.SIGKILL)
            os.waitpid(result["pid"], 0)

    def test_already_reaped_child_cleanup_is_idempotent(self):
        child = subprocess.Popen([sys.executable, "-c", "pass"], start_new_session=True)
        child.wait(timeout=2)
        self.assertIsNone(runner.kill(child))
        with patch.object(runner.os, "killpg", side_effect=PermissionError(1, "denied")) as group_signal:
            self.assertIsNone(runner.kill(child))
            group_signal.assert_not_called()


class FlexCorpusTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        (self.root / "generated").mkdir()
        (self.root / "archives").mkdir()
        rows = []
        for name, files in {
            "extra-small-lia": [("labelled.smt2", True, False), ("placeholder.smt2", False, True)],
            "hoice-regressions": [("unsat/control.smt2", None, False)],
        }.items():
            with tarfile.open(self.root / "archives" / f"{name}.tar.gz", "w:gz") as archive:
                for filename, verdict, placeholder in files:
                    member = f"upstream/{name}/{filename}"
                    path = self.root / "extracted" / name / filename
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text("(check-sat)\n" if verdict is None else "(assert true)\n(check-sat)\n")
                    rows.append(dict(archive=f"archives/{name}.tar.gz", archive_member=member,
                                     path="extracted/" + member, sha256=runner.digest(path),
                                     bytes=path.stat().st_size))
                    if verdict is not None:
                        label = (f"input_files: {Path(filename).name}\n"
                                 f"expected_verdict: {str(verdict).lower()}\n"
                                 + ("# placeholder\n" if placeholder else "")).encode()
                        info = tarfile.TarInfo(member.removesuffix(".smt2") + ".yml")
                        info.size = len(label)
                        archive.addfile(info, io.BytesIO(label))
            manifest = "manifest.json" if name == "extra-small-lia" else f"{name}-manifest.json"
            (self.root / "generated" / manifest).write_text(json.dumps(dict(
                input_root=f"/old/checkout/benchmarks/chc-smtlib/extracted/{name}",
                files=[dict(input=filename) for filename, _, _ in files])))
        with (self.root / "manifest.csv").open("w", newline="") as stream:
            writer = csv.DictWriter(stream, list(rows[0]))
            writer.writeheader()
            writer.writerows(rows)
        (self.root / "generated/summary.json").write_text(json.dumps(dict(
            suites=[dict(suite="extra-small-lia"), dict(suite="hoice-regressions")])))
        self.patch = patch.object(runner, "FLEX_CORPUS", self.root)
        self.patch.start()
        self.addCleanup(self.patch.stop)

    def test_labels_identity_and_controls_survive_adaptation(self):
        with patch.object(runner, "CORPUS", self.root / "unrelated-paper-corpus"):
            cases = runner.prepare("flex")
        labelled, placeholder, hoice = cases
        self.assertEqual(labelled["expected"], "sat")
        self.assertEqual(labelled["expected_source"], "CHC-COMP expected_verdict")
        self.assertTrue(labelled["candidate_eligible"])
        self.assertEqual(placeholder["declared_verdict"], "unsat")
        self.assertTrue(placeholder["placeholder_verdict"])
        self.assertIsNone(placeholder["expected"])
        self.assertEqual(hoice["expected"], "unsat")
        self.assertEqual(hoice["expected_source"], "upstream sat/unsat directory")
        self.assertTrue(hoice["has_query"])
        self.assertTrue(hoice["control"])
        self.assertFalse(hoice["candidate_eligible"])
        self.assertEqual(hoice["source_path"], "hoice-regressions/unsat/control.smt2")
        self.assertEqual(hoice["archive_member"], "upstream/hoice-regressions/unsat/control.smt2")
        self.assertTrue(all(c["corpus"] == "flex" and c["kind"] == "CHC" for c in cases))

    def test_modified_input_is_rejected(self):
        path = self.root / "extracted/extra-small-lia/labelled.smt2"
        path.write_text("(assert false)\n(check-sat)\n")
        with self.assertRaisesRegex(ValueError, "changed from pinned corpus"):
            runner.inputs()

    def test_summary_keeps_mismatches_and_excludes_controls_from_candidates(self):
        labelled, _, control = runner.inputs()
        records = [
            dict(case, solver=solver, status=status, seconds=0.1, limit_reason=None,
                 expected_mismatch=case is labelled and status == "unsat")
            for case, status in ((labelled, "unsat"), (control, "unknown"))
            for solver in ("spacer", "eldarica")
        ]
        summary, candidates = runner.summarize(records)
        self.assertEqual(summary["totals"]["spacer"]["expected_mismatches"], 1)
        self.assertEqual(summary["suites"]["extra-small-lia"]["eldarica"]["expected_mismatches"], 1)
        self.assertEqual(summary["solved_by_either"], 1)
        self.assertEqual(summary["solved_by_both"], 1)
        self.assertEqual(candidates, [])


if __name__ == "__main__":
    unittest.main()
