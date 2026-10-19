"""Focused process-cleanup tests; no benchmark solvers or corpus required."""

import importlib.util
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
from types import SimpleNamespace
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location(
    "solver_runner", Path(__file__).resolve().parents[2] / "scripts/evaluate_solvers.py")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


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


if __name__ == "__main__":
    unittest.main()
