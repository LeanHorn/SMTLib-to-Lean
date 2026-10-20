"""Focused lexical/LOC checks; no benchmark corpus or solver is needed."""

import sys
import json
from pathlib import Path
import shutil
import tempfile
import unittest


sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))
from evaluation import metrics


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

    def test_statement_section_keeps_options_local_and_excludes_scaffolding(self):
        block = "mutual\ninductive A where\n  | mk : B → A\ninductive B where\n  | mk : A → B\nend\n"
        for name in ["", " Statements"]:
            with self.subTest(name=name):
                prefix = ("import Init\nnamespace Demo\n-- Statements\n\n"
                          f"section{name}\nset_option Elab.async false\n\n"
                          + block + "def Refutation : Prop := True\n"
                          + f"end{name}\n\n")
                text = (prefix + "-- Proofs\ntheorem refutation : Refutation := by trivial\n"
                        "end Demo\n")
                statements, measured = metrics.split_generated_source(text)
                self.assertEqual(statements, prefix + "end Demo\n")
                self.assertEqual(measured, "-- Statements\n\n\n" + block
                                 + "def Refutation : Prop := True\n\n")

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
                     "section\ndef x := 0\n-- Proofs\n",
                     "namespace Demo\nsection\ndef x := 0\n-- Proofs\nend Demo\n",
                     "section Statements\ndef x := 0\nend Other\n-- Proofs\n",
                     "namespace Demo\nsection\ndef x := 0\nend Demo\n-- Proofs\n",
                     "mutual\ninductive A\nend\nend\n-- Proofs\n"]:
            with self.subTest(text=text), self.assertRaises(metrics.LexicalError):
                metrics.split_generated_source(text)


class StructureTests(unittest.TestCase):
    def test_input_counts_list_heads_and_exact_literal_bitvec_sorts(self):
        text = '''; (forall () (let () x)) (_ BitVec 999)
(set-info :source "(exists () true) (_ BitVec 512)")
(declare-fun |forall| ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 32))
(define-funs-rec ((f () Int) (g () Int)) (0 1))
(assert (forall ((x (_ BitVec 16)))
  (exists ((y Int)) (let ((z y)) (= |let| z)))))
(assert (= |forall| "(_ BitVec 128)"))
(set-info :ignored ((|forall| x) ("exists" x) (|let| x)
  (_ |BitVec| 64) (_ BitVec |64|) (_ BitVec 64 extra) (_ BitVec 00)))
'''
        result = metrics.input_structure(text)
        self.assertEqual(result["max_parenthesis_depth"], 6)
        self.assertEqual(result["quantifier_counts"], {"forall": 1, "exists": 1})
        self.assertEqual(result["quantifier_count"], 2)
        self.assertEqual(result["let_count"], 1)
        self.assertEqual(result["declaration_counts"],
                         {"declare-fun": 1, "define-funs-rec": 1})
        self.assertEqual(result["declaration_count"], 2)
        self.assertEqual(result["bitvec_sort_count"], 4)
        self.assertEqual(result["bitvec_widths"], [8, 16, 32])
        self.assertEqual(result["bitvec_width_min"], 8)
        self.assertEqual(result["bitvec_width_max"], 32)

    def test_input_empty_and_deep_nesting_without_recursion(self):
        empty = metrics.input_structure("; (forall x) (_ BitVec 1)\n")
        self.assertEqual(empty["max_parenthesis_depth"], 0)
        self.assertEqual(empty["declaration_counts"], {})
        self.assertEqual(empty["bitvec_widths"], [])
        self.assertIsNone(empty["bitvec_width_min"])
        self.assertIsNone(empty["bitvec_width_max"])
        depth = 12000
        result = metrics.input_structure("(" * depth + "x" + ")" * depth)
        self.assertEqual(result["max_parenthesis_depth"], depth)
        for text in ["(assert true", "(assert true))"]:
            with self.subTest(text=text), self.assertRaises(metrics.LexicalError):
                metrics.input_structure(text)

    def test_generated_structure_uses_emitted_boundaries_and_lexical_binders(self):
        first = "inductive A where\n  | mk : B → A\n"
        second = "inductive B where\n  | mk : A → B\n"
        declaration = '''noncomputable def target {α : Type} (x : α) : Prop :=
  ∀ (y : α), ∃ (z : α),
    let f := fun w => w
    let g := λ w => w
    (f (g x)) = x
'''
        text = ("import Init\nnamespace Demo\nsection\nset_option Elab.async false\n"
                "-- def bogus := ∀ (let)\n/- ∃ /- fun let -/ λ -/\n"
                "mutual\n" + first + second + "end\n" + declaration +
                'def «fun» := "∀ ∃ fun λ let ( [ {"\n'
                "def names := («forall», «let», 'λ')\n"
                "end\n-- Proofs\n"
                "theorem proof : ∀ x : Nat, x = x := by intro x; rfl\nend Demo\n")
        result = metrics.generated_structure(text)
        self.assertEqual(result["declaration_counts"], {"inductive": 2, "def": 3})
        self.assertEqual(result["declaration_count"], 5)
        self.assertEqual(result["largest_declaration_tokens"],
                         len(metrics.lean_tokens(declaration)))
        self.assertEqual(result["max_delimiter_depth"], 2)
        self.assertEqual(result["binder_token_counts"],
                         {"∀": 1, "forall": 0, "∃": 1, "fun": 1, "λ": 1})
        self.assertEqual(result["binder_token_count"], 4)
        self.assertEqual(result["let_count"], 2)

    def test_generated_mutual_wrappers_are_not_declaration_tokens(self):
        member = "inductive A where\n  | mk : A\n"
        result = metrics.generated_structure("mutual\n" + member + "end\n-- Proofs\n")
        self.assertEqual(result["largest_declaration_tokens"], len(metrics.lean_tokens(member)))
        self.assertEqual(result["declaration_counts"], {"inductive": 1})
        empty = metrics.generated_structure("import Init\n-- Proofs\n")
        self.assertEqual(empty["declaration_count"], 0)
        self.assertEqual(empty["largest_declaration_tokens"], 0)
        self.assertEqual(empty["max_delimiter_depth"], 0)

    def test_generated_delimiters_are_matched_and_scanned_iteratively(self):
        depth = 12000
        text = "def x := " + "(" * depth + "0" + ")" * depth + "\n-- Proofs\n"
        self.assertEqual(metrics.generated_structure(text)["max_delimiter_depth"], depth)
        mixed = "def x := ([{0}])\n-- Proofs\n"
        self.assertEqual(metrics.generated_structure(mixed)["max_delimiter_depth"], 3)
        for expression in ["([)]", "(0", "0)"]:
            with self.subTest(expression=expression), self.assertRaises(metrics.LexicalError):
                metrics.generated_structure(f"def x := {expression}\n-- Proofs\n")


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
            self.assertEqual(result["input_structure"], metrics.input_structure(source))
            self.assertEqual(result["output_structure"], metrics.generated_structure(generated))
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

    def test_input_only_cloc_matches_paired_measurement_and_keeps_artifacts(self):
        source = '''; (_ BitVec 1000)
(set-info :source "semi;colon
string continues")
(declare-const x (_ BitVec 8)) ; trailing
(assert (= x #x00))
'''
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp).resolve()
            result = metrics.measure_input(source, root / "input")
            paired = metrics.measure(source, "def p := True\n-- Proofs\n", root / "pair")
            for key in ["input_code_loc", "input_tokens", "input_bytes"]:
                self.assertEqual(result[key], paired[key])
            self.assertEqual(result["input_structure"], paired["input_structure"])
            self.assertEqual(result["input_code_loc"], 4)
            self.assertEqual(result["input_structure"]["bitvec_widths"], [8])
            command = json.loads((root / "input/cloc-command.json").read_text())
            self.assertEqual(command[-1], str(root / "input/input.masked.smt2"))
            self.assertTrue((root / "input/cloc.json").is_file())
            self.assertTrue((root / "input/cloc.stderr").is_file())
            self.assertIn('"semi;colon\nstring continues"',
                          (root / "input/input.masked.smt2").read_text())
            empty = metrics.measure_input("; only comments\n", root / "empty")
            self.assertEqual(empty["input_code_loc"], 0)
            self.assertEqual(empty["input_tokens"], 0)
            self.assertEqual(empty["input_bytes"], len("; only comments\n".encode()))


if __name__ == "__main__":
    unittest.main()
