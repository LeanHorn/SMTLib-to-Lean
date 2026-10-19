"""Focused lexical/LOC checks; no benchmark corpus or solver is needed."""

import importlib.util
import json
from pathlib import Path
import shutil
import tempfile
import unittest


spec = importlib.util.spec_from_file_location(
    "evaluation_metrics", Path(__file__).resolve().parents[2] / "scripts/evaluation_metrics.py")
metrics = importlib.util.module_from_spec(spec)
spec.loader.exec_module(metrics)


class LexicalTests(unittest.TestCase):
    def test_smt_strings_quoted_symbols_and_comment_commands(self):
        text = '''; (check-sat) (assert false)
(set-logic HORN)
(set-info :source "(check-sat) ""(rule x)""")
(declare-fun |semi;colon| () Bool)
(assert |semi;colon|)
(rule (=> p q))
(check-sat)
(check-sat-assuming (p))
(query q)
'''
        info = metrics.source_info(text)
        self.assertEqual(info["query_count"], 3)
        self.assertEqual(info["assertion_count"], 1)
        self.assertEqual(info["rule_count"], 1)
        self.assertEqual(info["constraint_count"], 2)
        self.assertEqual(info["logic"], "HORN")
        self.assertFalse(info["source_empty"])
        tokens = metrics.smt_tokens(text)
        self.assertIn('"(check-sat) ""(rule x)"""', tokens)
        self.assertEqual(tokens.count("|semi;colon|"), 2)
        self.assertEqual(metrics.smt_tokens('(assert (= x 1))'),
                         ["(", "assert", "(", "=", "x", "1", ")", ")"])

    def test_lean_nested_comments_literals_and_escaped_identifiers(self):
        text = '''/- outer /- inner -- comment -/ still outer -/
def «name /- --» := "quoted \\" -- /- text" -- actual comment
def x' := 12.5 + 0xFF
def c := '\\''
'''
        self.assertEqual(metrics.lean_tokens(text),
                         ["def", "«name /- --»", ":=", '"quoted \\" -- /- text"',
                          "def", "x'", ":=", "12.5", "+", "0xFF",
                          "def", "c", ":=", "'\\''"])

    def test_rejects_unfinished_or_unsupported_syntax(self):
        for text in ['"unfinished', '|unfinished', '(assert true', '(assert |a\\b|)']:
            with self.subTest(text=text), self.assertRaises(metrics.LexicalError):
                metrics.source_info(text)
        for text in ['/- /- inner -/', '"unfinished', '«unfinished', 'r#"raw"#', '`foo']:
            with self.subTest(text=text), self.assertRaises(metrics.LexicalError):
                metrics.lean_tokens(text)

    def test_empty_source(self):
        info = metrics.source_info("; only a comment\n")
        self.assertEqual(info["query_count"], 0)
        self.assertTrue(info["source_empty"])


class SplittingTests(unittest.TestCase):
    def test_proof_marker_in_comment_or_string_is_ignored_and_scope_is_kept(self):
        text = '''import Init
set_option maxRecDepth 4096
namespace Demo
-- Statements
/- preserved comment
-- Proofs
-/
def label := "line one
-- Proofs
line three"
def Refutation : Prop := False
-- Proofs
theorem refutation : Refutation := by
  sorry
end Demo
'''
        statements, measured = metrics.split_generated_source(text)
        self.assertTrue(statements.startswith("import Init\nset_option"))
        self.assertIn("namespace Demo\n", statements)
        self.assertTrue(statements.endswith("end Demo\n"))
        self.assertNotIn("theorem refutation", statements)
        self.assertNotIn("sorry", measured)
        self.assertNotIn("import Init", measured)
        self.assertNotIn("set_option", measured)
        self.assertNotIn("namespace Demo", measured)
        self.assertNotIn("end Demo", measured)
        self.assertIn("def Refutation : Prop := False", measured)
        self.assertIn("-- Proofs\nline three", measured)

    def test_exact_marker_and_namespace_validation(self):
        for text in ["def x := 0\n-- Proofs extra\n", "-- Proofs\n-- Proofs\n",
                     "namespace Demo\ndef x := 0\n-- Proofs\n",
                     "namespace Demo\ndef x := 0\n-- Proofs\nend Other\n"]:
            with self.subTest(text=text), self.assertRaises(metrics.LexicalError):
                metrics.split_generated_source(text)

    def test_nested_namespace_closures(self):
        text = "namespace A\nnamespace B\ndef x := 0\n-- Proofs\ntheorem y : True := by trivial\nend B\nend A\n"
        statements, measured = metrics.split_generated_source(text)
        self.assertEqual(statements, "namespace A\nnamespace B\ndef x := 0\nend B\nend A\n")
        self.assertEqual(measured, "def x := 0\n")

    def test_mutual_blocks_remain_in_statements_and_metrics(self):
        block = "mutual\ninductive A where\n  | mk : B → A\ninductive B where\n  | mk : A → B\nend\n"
        for opening, closing in [("", ""),
                                 ("namespace Outer\nnamespace Inner\n", "end Inner\nend Outer\n")]:
            with self.subTest(opening=opening):
                prefix = "import Init\n" + opening + block
                text = prefix + "-- Proofs\ntheorem example : True := by sorry\n" + closing
                statements, measured = metrics.split_generated_source(text)
                self.assertEqual(statements, prefix + closing)
                self.assertEqual(measured, block)

    def test_multiple_mutual_blocks_and_closed_namespace(self):
        block = "mutual\ninductive A where\n  | mk : B → A\ninductive B where\n  | mk : A → B\nend\n"
        prefix = "namespace First\n" + block + "end First\nnamespace Second\n" + block
        text = prefix + "-- Proofs\ntheorem example : True := by sorry\nend Second\n"
        statements, measured = metrics.split_generated_source(text)
        self.assertEqual(statements, prefix + "end Second\n")
        self.assertEqual(measured, block + block)

    def test_rejects_unclosed_and_mismatched_blocks(self):
        for text in ["mutual\ninductive A\n-- Proofs\n",
                     "namespace Demo\nmutual\ninductive A\n-- Proofs\nend Demo\n",
                     "namespace Demo\nmutual\ninductive A\nend Demo\n-- Proofs\n",
                     "namespace Demo\ndef x := 0\nend Other\n-- Proofs\n",
                     "mutual\ninductive A\nend\nend\n-- Proofs\n"]:
            with self.subTest(text=text), self.assertRaises(metrics.LexicalError):
                metrics.split_generated_source(text)


@unittest.skipUnless(shutil.which("cloc"), "cloc is not installed")
class ClocTests(unittest.TestCase):
    def test_actual_cloc_counts_literals_and_excludes_comments_and_scaffolding(self):
        source = '''; (check-sat)
(set-info :source "semi;colon
string continues")
(assert |semi;colon|) ; trailing
(check-sat)
'''
        generated = '''import Init
set_option maxRecDepth 4096
namespace Example
/- outer
/- nested -/
outer -/
def «name /- --» := "first /-
-- literal line
last -/"
def Refutation : Prop := False -- inline
-- Proofs
theorem refutation : Refutation := by
  sorry
end Example
'''
        with tempfile.TemporaryDirectory() as temp:
            result = metrics.measure(source, generated, temp)
            self.assertEqual(result["input_code_loc"], 4)
            self.assertEqual(result["output_code_loc"], 4)
            self.assertEqual(result["input_tokens"], len(metrics.smt_tokens(source)))
            self.assertEqual(result["output_tokens"], 10)
            self.assertEqual(result["input_bytes"], len(source.encode()))
            self.assertEqual(result["output_bytes"], len(generated.encode()))
            self.assertLess(result["output_statement_bytes"], result["output_bytes"])
            self.assertEqual(result["code_loc_ratio"], 1)
            artifact = Path(temp).resolve()
            self.assertIn('"semi;colon\nstring continues"', (artifact / "input.masked.smt2").read_text())
            self.assertIn('"first /-\n-- literal line', (artifact / "output.masked.txt").read_text())
            self.assertNotIn('/-', (artifact / "output.cloc.lean").read_text())
            self.assertEqual((artifact / "output.masked.txt").read_text().count("\n"),
                             (artifact / "output.cloc.lean").read_text().count("\n"))
            report = json.loads((artifact / "cloc.json").read_text())
            self.assertEqual(report[str(artifact / "output.cloc.lean")]["language"], "Lean")
            self.assertEqual(report[str(artifact / "input.masked.smt2")]["language"], "SMT-LIB")

    def test_zero_denominator_yields_null_ratios(self):
        with tempfile.TemporaryDirectory() as temp:
            result = metrics.measure("", "import Init\n-- Proofs\n", temp)
            self.assertEqual(result["input_code_loc"], 0)
            self.assertEqual(result["output_code_loc"], 0)
            for key in ["code_loc_ratio", "token_ratio", "byte_ratio", "statement_byte_ratio"]:
                self.assertIsNone(result[key])


if __name__ == "__main__":
    unittest.main()
