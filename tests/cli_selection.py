"""Check CLI test selection and compilation policy without starting Lean."""

import contextlib
import io
from pathlib import Path
import shlex
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import cli
from cli_checks import support


class SelectionTests(unittest.TestCase):
    def run_groups(self, args):
        calls = []

        def record(name, lean, temporary):
            self.assertEqual(str(lean), "/lean/bin/lean")
            self.assertTrue(temporary.is_dir())
            calls.append((name, temporary))

        groups = {name: (lambda lean, tmp, name=name: record(name, lean, tmp),)
                  for name in cli.GROUPS}
        with patch.dict(cli.GROUPS, groups, clear=True), \
                patch.object(cli.subprocess, "check_output", return_value="/lean\n"), \
                contextlib.redirect_stdout(io.StringIO()):
            cli.main(args)
        self.assertTrue(all(not temporary.exists() for _, temporary in calls))
        self.assertEqual(len({temporary for _, temporary in calls}), len(calls))
        return [name for name, _ in calls]

    def test_no_arguments_runs_all_groups(self):
        self.assertEqual(self.run_groups([]), list(cli.GROUPS))

    def test_selected_groups_only_and_no_repetition(self):
        self.assertEqual(self.run_groups(["horn"]), ["horn"])
        self.assertEqual(self.run_groups(["sessions", "horn", "sessions"]),
                         ["sessions", "horn"])

    def test_unknown_group_fails_before_running_anything(self):
        with patch.object(cli.subprocess, "check_output") as process, \
                contextlib.redirect_stderr(io.StringIO()), \
                self.assertRaises(SystemExit) as error:
            cli.main(["horn", "typo"])
        self.assertEqual(error.exception.code, 2)
        process.assert_not_called()

    def test_listing_and_help_do_not_start_lean(self):
        output = io.StringIO()
        with patch.object(cli.subprocess, "check_output") as process, \
                contextlib.redirect_stdout(output):
            cli.main(["--list"])
            self.assertEqual(output.getvalue().splitlines(), list(cli.GROUPS))
            with self.assertRaises(SystemExit) as error:
                cli.main(["--help"])
        self.assertEqual(error.exception.code, 0)
        process.assert_not_called()

    def test_pass_reports_duration_and_removes_artifacts(self):
        output = io.StringIO()
        # The normal selection tests verify successful directories are removed.
        with patch.dict(cli.GROUPS, {"horn": (lambda *_: print("check details"),)}), \
                patch.object(cli.subprocess, "check_output", return_value="/lean\n"), \
                patch.object(cli.time, "perf_counter", side_effect=[10, 12.5]), \
                contextlib.redirect_stdout(output):
            self.assertEqual(cli.main(["horn"]), 0)
        self.assertIn("PASS horn (2.50s)", output.getvalue())
        self.assertNotIn("check details", output.getvalue())

    def test_failure_and_interruption_preserve_evidence_and_stop(self):
        for error, code, status in [(AssertionError("sentinel"), 1, "FAIL"),
                                    (KeyboardInterrupt(), 130, "INTERRUPTED")]:
            with self.subTest(status=status), tempfile.TemporaryDirectory() as parent:
                artifact = Path(parent) / "failed group"
                artifact.mkdir()
                output = io.StringIO()
                calls = []

                def fail(lean, tmp):
                    (tmp / "Query.lean").write_text("failure evidence")
                    print("stdout evidence")
                    print("stderr evidence", file=sys.stderr)
                    raise error

                with patch.dict(cli.GROUPS, {"horn": (fail,),
                                            "core": (lambda *_: calls.append("core"),)}), \
                        patch.object(cli.subprocess, "check_output", return_value="/lean\n"), \
                        patch.object(cli.tempfile, "mkdtemp", return_value=str(artifact)), \
                        patch.object(cli.time, "perf_counter", side_effect=[10, 12.5]), \
                        patch.object(cli, "ROOT", Path("/repo with spaces")), \
                        contextlib.redirect_stdout(output):
                    self.assertEqual(cli.main(["horn", "core"]), code)
                self.assertEqual(calls, [])
                self.assertEqual((artifact / "Query.lean").read_text(), "failure evidence")
                log = (artifact / "checks.log").read_text()
                for text in ["Check: fail", "stdout evidence", "stderr evidence",
                             "Traceback", type(error).__name__]:
                    self.assertIn(text, log)
                report = output.getvalue()
                self.assertIn(f"{status} horn (2.50s)", report)
                self.assertIn(str(artifact / "checks.log"), report)
                command = report.split("Rerun: ", 1)[1].strip()
                self.assertEqual(shlex.split(command),
                                 ["cd", "/repo with spaces", "&&", "lake", "env",
                                  "python3", "tests/cli.py", "horn"])
                self.assertNotIn("CLI groups passed", report)


class CompilationTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.output = Path(self.directory.name)
        self.query = self.output / "Query.lean"
        self.source = (support.FIXTURES / "expected/Query.lean").read_text()
        self.query.write_text(self.source)

    def compiler(self):
        return patch.object(support.subprocess, "run",
                            return_value=subprocess.CompletedProcess([], 0, "", ""))

    def test_statements_compile_once_without_admissions(self):
        with self.compiler() as compiler:
            support.check_generated("lean", self.output)
        compiler.assert_called_once()
        args = compiler.call_args.args[0]
        self.assertIn("--error=hasSorry", args)
        self.assertEqual(args[-1], "StatementsOnly.lean")
        self.assertEqual(self.query.read_text(), self.source)
        self.assertFalse((self.output / "StatementsOnly.lean").exists())

    def test_template_is_explicit_and_still_checks_statements(self):
        with self.compiler() as compiler:
            support.check_generated("lean", self.output, template=True)
        calls = [call.args[0] for call in compiler.call_args_list]
        self.assertEqual([args[-1] for args in calls], ["Query.lean", "StatementsOnly.lean"])
        self.assertNotIn("--error=hasSorry", calls[0])
        self.assertIn("--error=hasSorry", calls[1])

    def test_completed_proof_compiles_once(self):
        with self.compiler() as compiler:
            source = support.read_generated(self.output)
            compiler.assert_not_called()
            self.query.write_text(source.replace("  sorry\n", "  intro p h\n  exact h.2 h.1\n"))
            support.check_lean("lean", self.query, complete=True)
        compiler.assert_called_once()
        self.assertIn("--error=hasSorry", compiler.call_args.args[0])
        self.assertIn("-DwarningAsError=true", compiler.call_args.args[0])

    def test_compilation_failure_is_not_ignored(self):
        with patch.object(support.subprocess, "run",
                          return_value=subprocess.CompletedProcess([], 1, "failure", "")), \
                self.assertRaisesRegex(AssertionError, "failure"):
            support.check_generated("lean", self.output)


if __name__ == "__main__":
    unittest.main()
