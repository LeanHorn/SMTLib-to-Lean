"""Runner regressions: real Lean checks, controlled translator failures, temporary files."""

import argparse
from contextlib import redirect_stderr
import csv
import importlib.util
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("anchor", ROOT / "benchmarks/run.py")
anchor = importlib.util.module_from_spec(spec)
spec.loader.exec_module(anchor)

# A controlled executable isolates process/reporting behavior from translator semantics.
TRANSLATOR = '''#!/usr/bin/env python3
import os
from pathlib import Path
import signal
import sys
import time
text = Path(sys.argv[1]).read_text()
if '; timeout' in text:
    time.sleep(20)
if '; crash' in text:
    os.kill(os.getpid(), signal.SIGTERM)
if '; unsupported' in text:
    sys.stderr.write('smt2lean: cvc5.Error.unsupported "unsupported test operator"\\n')
    sys.exit(1)
if '; backend_error' in text:
    sys.stderr.write('smt2lean: cvc5.Error.error "malformed input"\\n')
    sys.exit(1)
if '; error' in text:
    sys.stderr.write('smt2lean: reconstruction failed for symbol unsupported\\n')
    sys.exit(1)
out = Path(sys.argv[3])
assert sys.argv[4] == '--max-rec-depth'
depth = int(sys.argv[5])
out.mkdir()
body = 'True'
if '; unused' in text:
    body = '∀ (x : Int), True'
if '; admission' in text:
    body = 'by sorry'
if '; type_error' in text:
    body = '(37 : Nat)'
proof = 'by sorry' if '; bad_template' not in text else 'by exact (37 : Nat)'
(out / 'Query.lean').write_text('import Init\\n\\nset_option maxRecDepth ' + str(depth) +
    '\\n\\n-- Statements\\n\\ndef Refutation : Prop := ' + body +
    '\\n\\n-- Proofs\\n\\ntheorem refutation : Refutation := ' + proof + '\\n')
'''


class AnchorTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        prefix = subprocess.check_output(["lean", "--print-prefix"], cwd=ROOT, text=True).strip()
        cls.lean = Path(prefix) / "bin/lean"

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="smt2lean anchor ")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.executable = self.root / "translator"
        self.executable.write_text(TRANSLATOR)
        self.executable.chmod(0o755)
        self.args = argparse.Namespace(max_input_mib=1, max_file_mib=1,
                                      translation_timeout=2, lean_timeout=15, lean_memory_mib=512,
                                      max_rec_depth=4096)

    def case(self, mode, *, text=None, selection=None):
        path = self.root / (mode + ".smt2")
        path.write_text(text or f"; {mode}\n(set-logic QF_UF)\n(check-sat)\n")
        directory = self.root / mode
        directory.mkdir()
        record = dict(path=str(path), selection=selection or {}, stages={}, outcome="not_run",
                      translation_status="not_run", statements_status="not_run", template_status="not_run")
        with patch.object(anchor, "EXE", self.executable):
            anchor.check_case(record, directory, self.args, self.lean, dict(os.environ))
        return record, directory

    def test_real_typecheck_keeps_lint_warnings_separate(self):
        record, directory = self.case("unused")
        self.assertEqual(record["outcome"], "passed")
        self.assertEqual(record["statements_warnings"], 1)
        self.assertEqual(record["template_admissions"], 1)
        self.assertEqual(record["emitted_queries"], 1)
        self.assertTrue((directory / "generated/Query.lean").is_file())
        self.assertIn("linter.unusedVariables", record["stages"]["statements"]["warnings"])

    def test_admitted_statement_fails_even_when_template_checks(self):
        record, _ = self.case("admission")
        self.assertEqual(record["outcome"], "statements_error")
        self.assertEqual(record["statements_status"], "error")
        self.assertEqual(record["template_status"], "passed")
        self.assertIn("sorry", record["reason"])

    def test_type_errors_and_template_errors_are_separate(self):
        statement, _ = self.case("type_error")
        self.assertEqual(statement["statements_status"], "error")
        self.assertEqual(statement["template_status"], "error")
        template, _ = self.case("bad_template")
        self.assertEqual(template["statements_status"], "passed")
        self.assertEqual(template["outcome"], "template_error")

    def test_failed_translation_never_reports_typechecked(self):
        for mode in ("unsupported", "backend_error", "error", "timeout", "crash"):
            with self.subTest(mode=mode):
                self.args.translation_timeout = 0.2 if mode == "timeout" else 2
                record, directory = self.case(mode)
                self.assertEqual(record["translation_status"], mode)
                self.assertEqual(record["statements_status"], "not_run")
                self.assertEqual(record["template_status"], "not_run")
                self.assertTrue((directory / "translation.stderr.log").exists())
                self.assertGreater(record["translation_seconds"], 0)

    def test_pinned_hash_and_size_limits_prevent_execution(self):
        record, directory = self.case("changed", selection={"sha256": "0" * 64})
        self.assertEqual(record["outcome"], "hash_mismatch")
        self.assertEqual(record["stages"], {})
        self.assertFalse((directory / "generated").exists())
        record, _ = self.case("large", text=";" * (anchor.MIB + 1))
        self.assertEqual(record["outcome"], "input_limit")
        self.assertEqual(record["stages"], {})

    def test_incomplete_sessions_cannot_pass(self):
        record, _ = self.case("session", text="(check-sat)\n(check-sat)\n")
        self.assertEqual(record["outcome"], "output_error")
        self.assertEqual(record["input_queries"], 2)
        self.assertEqual(record["emitted_queries"], 1)

    def test_metadata_ignores_comments_strings_and_quoted_symbols(self):
        text = '''; (check-sat)
        (set-info :source "(check-sat) ""(set-logic HORN)""")
        (set-logic QF_UF)
        (declare-const |(check-sat)| Bool)
        (check-sat)
        (check-sat-assuming (|(check-sat)|))'''
        self.assertEqual(anchor.source_info(text), {"input_queries": 2, "logic": "QF_UF", "kind": "SMT"})

    def test_directories_lists_duplicates_and_missing_paths(self):
        folder = self.root / "inputs with spaces"
        folder.mkdir()
        (folder / "a.smt2").write_text("(check-sat)")
        listing = self.root / "paths.txt"
        listing.write_text("# comment\ninputs with spaces/a.smt2\nmissing.smt2\n")
        records = anchor.select_inputs([folder], [listing])
        self.assertEqual(len(records), 2)
        self.assertEqual(Path(records[1]["path"]).name, "missing.smt2")
        csv_path = self.root / "pin.csv"
        with csv_path.open("w", newline="") as stream:
            writer = csv.writer(stream)
            writer.writerow(["path", "sha256", "category"])
            writer.writerow(["a.smt2", "a" * 64, "test"])
        records = anchor.select_inputs([], [csv_path], folder)
        self.assertEqual(records[0]["path"], str((folder / "a.smt2").resolve()))
        self.assertEqual(records[0]["selection"]["category"], "test")

    def test_file_limit_and_timeout_kill_subprocesses(self):
        result = anchor.run_process([sys.executable, "-c", "import os; os.write(1,b'x'*1000000); os.write(1,b'x')"],
                                    self.root, "limit", 5, 1024, cwd=self.root, env=dict(os.environ))
        self.assertNotEqual(result["status"], "passed")
        self.assertLessEqual((self.root / "limit.stdout.log").stat().st_size, 1024)
        started, survived = self.root / "started", self.root / "survived"
        descendant = "import pathlib,sys,time; pathlib.Path(sys.argv[1]).touch(); time.sleep(1); pathlib.Path(sys.argv[2]).touch()"
        program = "import subprocess,sys,time; subprocess.Popen([sys.executable,'-c',sys.argv[1],sys.argv[2],sys.argv[3]]); time.sleep(20)"
        result = anchor.run_process([sys.executable, "-c", program, descendant, str(started), str(survived)], self.root,
                                    "timeout", 0.5, 1024, cwd=self.root, env=dict(os.environ))
        self.assertEqual(result["status"], "timeout")
        self.assertTrue(started.exists())
        time.sleep(0.8)
        self.assertFalse(survived.exists(), "Descendant survived the stage timeout")

    def test_cli_records_all_results_and_refuses_overwrite(self):
        unsupported = self.root / "unsupported.smt2"
        unsupported.write_text('(set-logic QF_S)\n(declare-const s String)\n(check-sat)\n')
        valid = self.root / "valid.smt2"
        valid.write_text('(set-logic QF_UF)\n(assert false)\n(check-sat)\n')
        out = self.root / "run"
        command = [sys.executable, str(ROOT / 'benchmarks/run.py'), str(self.root / 'missing.smt2'),
                   str(unsupported), str(valid), '--out', str(out), '--max-rec-depth', '8192']
        first = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=90)
        self.assertEqual(first.returncode, 1, first.stderr)
        with (out / 'results.csv').open(newline='') as stream:
            rows = list(csv.DictReader(stream))
        self.assertEqual([r['outcome'] for r in rows], ['input_error', 'translation_unsupported', 'passed'])
        metadata = json.loads((out / 'run.json').read_text())
        self.assertEqual(metadata['status'], 'complete')
        self.assertEqual(metadata['arguments']['max_rec_depth'], 8192)
        generated = out / rows[-1]['artifacts'] / 'generated/Query.lean'
        self.assertIn('set_option maxRecDepth 8192\n', generated.read_text())
        before = (out / 'run.json').read_bytes()
        second = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=30)
        self.assertEqual(second.returncode, 2)
        self.assertEqual((out / 'run.json').read_bytes(), before)

    def test_cli_rejects_invalid_recursion_depth_before_creating_output(self):
        output = self.root / 'invalid-depth'
        for depth in ['0', '-1', 'bad']:
            with self.subTest(depth=depth), redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as error:
                anchor.main(['--out', str(output), '--max-rec-depth', depth])
            self.assertEqual(error.exception.code, 2)
            self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
