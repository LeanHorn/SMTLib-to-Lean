"""Check CLI test selection without starting Lean or the translator."""

import contextlib
import io
import unittest
from unittest.mock import patch

import cli


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

    def test_check_failure_propagates(self):
        with patch.dict(cli.GROUPS, {"horn": (lambda *_: self.fail("sentinel"),)}), \
                patch.object(cli.subprocess, "check_output", return_value="/lean\n"), \
                contextlib.redirect_stdout(io.StringIO()), \
                self.assertRaisesRegex(AssertionError, "sentinel"):
            cli.main(["horn"])


if __name__ == "__main__":
    unittest.main()
