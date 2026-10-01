"""Run with `lake env python3 tests/cli.py` after `lake build smt2lean`."""

from pathlib import Path
import os
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
EXE = ROOT / ".lake/build/bin/smt2lean"
FIXTURES = ROOT / "tests/translation/bool"
INTEGERS = ROOT / "tests/translation/int"
FUNCTIONS = ROOT / "tests/translation/functions"
QUANTIFIERS = ROOT / "tests/translation/quantifiers"
BINDINGS = ROOT / "tests/translation/bindings"
CHC = ROOT / "tests/translation/chc"
SESSIONS = ROOT / "tests/translation/sessions"
SOLVER_OPTIONS = """(set-option :produce-models true)
(set-option :produce-proofs true)
(set-option :produce-unsat-cores true)
(set-option :print-success true)
(set-option :random-seed 42)
"""


def run(*args, code=0):
    args = [arg.relative_to(ROOT) if isinstance(arg, Path) and arg.is_relative_to(ROOT)
            else arg for arg in args]
    result = subprocess.run(
        [str(EXE), *map(str, args)], cwd=ROOT, capture_output=True, text=True
    )
    assert result.returncode == code, (args, result.returncode, result.stdout, result.stderr)
    if code:
        assert result.stderr and not result.stdout, result
    return result


def without_sources(text):
    """Metadata and filenames may move locations, but must not change Lean code."""
    return "".join(line for line in text.splitlines(keepends=True)
                   if not line.startswith("-- Source: "))


def check_lean(lean, source, *, complete=False):
    args = [str(lean)]
    if complete:
        args.append("-DwarningAsError=true")
    # Core-only files must remain independent of all project packages.
    search_path = str(source.parent)
    if any(line.startswith("import Mathlib.") for line in source.read_text().splitlines()):
        search_path += os.pathsep + os.environ["LEAN_PATH"]
    result = subprocess.run(
        [*args, source.name], cwd=source.parent,
        env=dict(os.environ, LEAN_PATH=search_path),
        capture_output=True, text=True,
    )
    assert result.returncode == 0, (source, result.stdout, result.stderr)
    return result.stdout


def check_generated(lean, output, *, goal="Refutation", count=1):
    assert [p.name for p in output.iterdir()] == ["Query.lean"]
    query = output / "Query.lean"
    source = query.read_text()
    statements, proofs = source.split("-- Proofs\n", 1)
    assert statements.count("-- Statements") == 1
    assert "-- Source: " in statements
    assert "sorry" not in statements and "by\n  sorry" in proofs
    assert proofs.count("theorem ") == count and "def " not in proofs
    assert statements.count(f"def {goal}") == count
    for number in range(1, count + 1):
        name = goal if count == 1 else f"{goal}_{number}"
        assert f"def {name} : Prop" in statements
        assert f"theorem {name.lower()} : {name}" in proofs
        if count > 1:
            assert re.search(rf"\(query {number}: check-sat(?:-assuming)?,", statements)
    check_lean(lean, query)
    # The statement must also compile after removing the unfinished proof entirely.
    standalone = output / "StatementsOnly.lean"
    standalone.write_text(statements)
    check_lean(lean, standalone)
    standalone.unlink()
    return source


def check_resets(lean, tmp):
    """Check resets, observation requests, and logic changes through the actual CLI."""
    for name, body, reason in [
        ("reset-scope", "(set-logic ALL)(push 1)(reset-assertions)(pop 1)", "exceeds active scope"),
        ("reset-symbol", "(set-logic ALL)(declare-const p Bool)(reset-assertions)(assert p)", "not declared"),
        ("reset-definition", "(set-logic ALL)(define-fun p () Bool true)(reset-assertions)(assert p)", "not declared"),
        ("reset-global", "(set-option :global-declarations true)(set-logic ALL)(declare-const p Bool)(reset)(set-logic ALL)(assert p)", "not declared"),
        ("late-result", "(set-logic ALL)(check-sat)(assert true)(get-model)", "requires a preceding check"),
        ("named-request", "(set-logic ALL)(check-sat)(get-value ((! true :named leak)))", "cannot introduce named terms"),
        ("bad-global", '(set-option :global-declarations "true")', "requires true or false"),
    ]:
        source, output = tmp / f"{name}.smt2", tmp / name
        source.write_text(body)
        result = run(source, "--out", output, code=1)
        assert reason in result.stderr and not output.exists(), result.stderr
    source, output = tmp / "skipped.smt2", tmp / "skipped"
    source.write_text("(set-logic ALL)(assert false)(check-sat)(get-model)(get-proof)(get-unsat-core)(get-unsat-assumptions)(get-assignment)(get-assertions)(get-info :name)(get-option :produce-models)(get-value (true))")
    result = run(source, "--out", output)
    text = check_generated(lean, output)
    assert text.count("-- Not executed:") == 9
    assert not {"sat", "unsat", "unknown"}.intersection(result.stdout.splitlines())

    source, output = tmp / "reset-logic.smt2", tmp / "reset-logic"
    source.write_text("(set-logic QF_UF)(assert false)(check-sat)(reset)(set-logic HORN)(declare-const p Bool)(check-sat-assuming (p))(reset)(set-logic QF_LIA)(declare-const x Int)(assert (< x 0))(check-sat)")
    run(source, "--out", output)
    query = output / "Query.lean"
    text = query.read_text()
    assert all(f"def {name} : Prop" in text for name in ["Refutation_1", "Problem_2", "Refutation_3"])
    check_lean(lean, query)
    query.write_text(text.split("-- Proofs\n", 1)[0])
    check_lean(lean, query)


def check_uninterpreted_sorts(lean, tmp):
    """Prove distinguishing examples, so a fixed or empty carrier cannot pass."""
    output = tmp / "sort-horn-demo"
    run(CHC / "uninterpreted.smt2", "--out", output)
    check_generated(lean, output, goal="Problem")
    cases = [
        ("nonempty", "UF", "(assert (forall ((_x S)) false))", "Refutation",
         "  intro A h allFalse\n  exact h.elim allFalse\n"),
        ("singleton", "UF", "(assert (forall ((x S) (y S)) (= x y)))", "¬ Refutation",
         "  intro h\n  exact h Unit ⟨()⟩ (fun x y => Subsingleton.elim x y)\n"),
        ("two-elements", "QF_UF", "(declare-const a S)(declare-const b S)(assert (distinct a b))",
         "¬ Refutation", "  intro h\n  exact h Bool ⟨false⟩ true false (by change true ≠ false; decide)\n"),
        ("infinite", "UF", "(declare-fun next (S) S)(declare-const zero S)"
         "(assert (forall ((x S) (y S)) (=> (= (next x) (next y)) (= x y))))"
         "(assert (forall ((x S)) (not (= (next x) zero))))", "¬ Refutation",
         "  intro h\n  exact h Nat ⟨0⟩ Nat.succ 0 ⟨fun _ _ e => Nat.succ.inj e, fun _ e => Nat.noConfusion e⟩\n"),
        ("horn-singleton", "HORN", "(declare-fun P (S) Bool)"
         "(assert (forall ((x S)) (P x)))"
         "(assert (forall ((x S) (y S)) (=> (and (P x) (P y) (distinct x y)) false)))",
         "Problem", "  refine ⟨Unit, ⟨()⟩, (fun _ => True), ?_, ?_⟩\n"
         "  · intro _; trivial\n  · intro x y _ _ different; exact different (Subsingleton.elim x y)\n"),
        ("horn-nonempty", "HORN", "(assert (forall ((_x S)) false))", "¬ Problem",
         "  rintro ⟨A, ⟨a⟩, allFalse⟩\n  exact allFalse a\n"),
    ]
    for name, logic, body, target, proof in cases:
        source, output = tmp / f"sort-{name}.smt2", tmp / f"sort-{name}"
        source.write_text(f"(set-logic {logic})(declare-sort S 0){body}(check-sat)")
        run(source, "--out", output)
        goal = "Problem" if logic == "HORN" else "Refutation"
        generated = check_generated(lean, output, goal=goal)
        statements = generated.split("-- Proofs\n", 1)[0]
        completed = output / "Query.lean"
        completed.write_text(statements + f"theorem checked : {target} := by\n" + proof)
        check_lean(lean, completed, complete=True)
    for name, prefix, suffix, reason in [
        ("arity", "(set-logic ALL)(check-sat)", "(declare-sort S 1)", "only arity 0"),
        ("popped-sort", "(set-logic ALL)(push 1)(declare-sort S 0)(check-sat)",
         "(pop 1)(declare-const x S)", "not declared"),
        ("reset-sort", "(set-option :global-declarations true)(set-logic ALL)(declare-sort S 0)(check-sat)",
         "(reset)(set-logic ALL)(declare-const x S)", "not declared"),
        ("removed-alias", "(set-logic ALL)(declare-sort S 0)(define-sort Alias () S)(check-sat)",
         "(reset-assertions)(declare-const x Alias)", "not declared"),
        ("horn-constant", "(set-logic HORN)(declare-sort S 0)(check-sat)",
         "(declare-const x S)(check-sat)", "unsupported CHC declaration"),
        ("horn-function", "(set-logic HORN)(declare-sort S 0)(check-sat)",
         "(declare-fun f (S) S)(check-sat)", "unsupported CHC declaration"),
        ("horn-negative", "(set-logic HORN)(declare-sort S 0)(declare-fun P (S) Bool)(check-sat)",
         "(assert (forall ((x S)) (=> (not (P x)) false)))(check-sat)", "CHC relation inside"),
    ]:
        source, output = tmp / f"sort-bad-{name}.smt2", tmp / f"sort-bad-{name}"
        source.write_text(prefix + suffix)
        result = run(source, "--out", output, code=1)
        assert "query 2:" in result.stderr and reason in result.stderr, result.stderr
        assert not output.exists()
    print("Sort semantics passed: nonempty, singleton, two-element, infinite, and Horn models; later failures leave no output")


def check_integer_division(lean, tmp):
    """Check model choices at zero and translate the complete original CHC corpus."""
    for fixture, goal in [(INTEGERS / "division.smt2", "Refutation"), (CHC / "division.smt2", "Problem")]:
        output = tmp / f"division-{goal}"
        run(fixture, "--out", output)
        generated = check_generated(lean, output, goal=goal)
        assert generated.count("def SMT.intDiv ") == generated.count("def SMT.intMod ") == 1
    total = 0
    for name, clauses in [("lh_sum_rec", 3), ("lh_abs_neg", 5), ("flux_sum_off_by_one", 5), ("flux_bsearch", 15)]:
        output = tmp / f"corpus-{name}"
        run(ROOT / f"tests/chc/{name}.smt2", "--out", output)
        generated = check_generated(lean, output, goal="Problem")
        assert generated.count("(clause ") == clauses, name
        assert "divZero" not in generated and "modZero" not in generated, name
        total += clauses
    assert total == 28
    cases = [
        ("negative-divisor", "ALL", "(assert (not (= (div (- 5) (- 2)) 3)))", "Refutation",
         "  intro h\n  exact h (by decide)\n"),
        ("zero-choices", "ALL", "(assert (= (div 0 0) 7))(assert (= (div 1 0) 9))(assert (= (mod 0 0) (- 4)))",
         "¬ Refutation", "  intro h\n  apply h (fun x => if x = 0 then 7 else 9) (fun _ => -4)\n"
         "  simp [SMT.intDiv, SMT.intMod]\n"),
        ("congruence", "ALL", "(declare-const x Int)(declare-const y Int)(assert (= x y))"
         "(assert (distinct (div x 0) (div y 0)))", "Refutation",
         "  intro d x y h\n  exact h.2 (congrArg (fun z => SMT.intDiv d z 0) h.1)\n"),
        ("quantifier-sharing", "ALL", "(assert (forall ((x Int)) (= (div x 0) x)))"
         "(assert (distinct (div 5 0) 5))", "Refutation",
         "  intro d h\n  exact h.2 (h.1 5)\n"),
        ("horn-witness", "HORN", "(declare-fun P (Int) Bool)(assert (P (div 0 0)))"
         "(assert (forall ((x Int)) (=> (and (P x) (distinct x 7)) false)))", "Problem",
         "  refine ⟨(fun _ => 7), (fun x => x = 7), ?_, ?_⟩\n"
         "  · rfl\n  · intro x equal different; exact different equal\n"),
        ("horn-sharing", "HORN", "(assert (=> (distinct (mod 0 0) 7) false))"
         "(assert (=> (= (mod 0 0) 7) false))", "¬ Problem",
         "  rintro ⟨m, first, second⟩\n  by_cases h : SMT.intMod m 0 0 = 7\n"
         "  · exact second h\n  · exact first h\n"),
    ]
    for name, logic, body, target, proof in cases:
        source, output = tmp / f"division-{name}.smt2", tmp / f"division-{name}"
        source.write_text(f"(set-logic {logic}){body}(check-sat)")
        run(source, "--out", output)
        generated = check_generated(lean, output, goal="Problem" if logic == "HORN" else "Refutation")
        completed = output / "Query.lean"
        completed.write_text(generated.split("-- Proofs\n", 1)[0] + f"theorem checked : {target} := by\n" + proof)
        check_lean(lean, completed, complete=True)
    print("Integer division passed: six completed semantic proofs; all four original CHCs elaborate with 28 clauses")


def check_reals(lean, tmp):
    """Exact Real arithmetic and model choices, compiled using the pinned Mathlib profile."""
    for fixture, goal in [(ROOT / "tests/translation/real/arithmetic.smt2", "Refutation"),
                          (CHC / "real.smt2", "Problem")]:
        output = tmp / f"real-{goal}"
        run(fixture, "--out", output)
        generated = check_generated(lean, output, goal=goal)
        assert generated.startswith("import Mathlib.Data.Real.Basic\n")
        assert generated.count("noncomputable def SMT.realDiv ") == 1
    exact_cases = [
        "(= (+ 0.1 0.2) 0.3)",
        "(= (- 1.5 0.25 0.125) 1.125)",
        "(= (* (- 0.5) 2.0 3.0) (- 3.0))",
        "(= (/ 12.0 2.0 3.0) 2.0)",
        "(= (/ (- 1) 3) (- (/ 1.0 3.0)))",
        "(= (/ 3.0 (- 0.5)) (- 6.0))",
        "(= (abs (- 0.125)) 0.125)",
        "(and (< (- 2) (- 1) 0.0) (<= 0 0.1 0.1) (> 2 1 0.5) (>= 1.0 1 0))",
        "(distinct 0.1 0.2 0.3)",
        "(= (ite (< 0.1 0.2) 0.3 0.4) 0.3)",
        "(= (/ 2.5 0.5) 5.0)",
        "(= 340282366920938463463374607431768211457.00000000000000000001 "
        "(/ 34028236692093846346337460743176821145700000000000000000001.0 100000000000000000000.0))",
        "(= 0.00000000000000000001 (/ 1.0 100000000000000000000.0))",
    ]
    cases = [
        ("exact", "ALL", "(assert (not (and " + " ".join(exact_cases) + ")))", "Refutation",
         "  intro h\n  apply h\n  norm_num [SMT.distinct3]\n"),
        ("composite-divisor", "ALL", "(assert (distinct (/ 1.0 (/ 1.0 2.0)) 2.0))", "Refutation",
         "  intro d h\n  apply h\n  norm_num [SMT.realDiv]\n"),
        ("zero-choices", "ALL", "(assert (= (/ 0.0 0.0) 7.0))(assert (= (/ 1.0 0.0) 9.0))", "¬ Refutation",
         "  intro h\n  apply h (fun x => if x = 0 then 7 else 9)\n  norm_num [SMT.realDiv]\n"),
        ("congruence", "ALL", "(declare-const x Real)(declare-const y Real)(assert (= x y))"
         "(assert (distinct (/ x 0.0) (/ y 0.0)))", "Refutation",
         "  intro d x y h\n  exact h.2 (congrArg (fun z => SMT.realDiv d z 0) h.1)\n"),
        ("quantifier-sharing", "ALL", "(assert (forall ((x Real)) (= (/ x 0.0) x)))"
         "(assert (distinct (/ 5.0 0.0) 5.0))", "Refutation",
         "  intro d h\n  exact h.2 (h.1 5)\n"),
        ("independent-zero-cases", "ALL", "(assert (= (div 0 0) 1))(assert (= (mod 0 0) 2))"
         "(assert (= (/ 0.0 0.0) 3.0))", "¬ Refutation",
         "  intro h\n  apply h (fun _ => 1) (fun _ => 2) (fun _ => 3)\n"
         "  norm_num [SMT.intDiv, SMT.intMod, SMT.realDiv]\n"),
        ("horn-linear", "HORN", "(declare-fun P (Real) Bool)(assert (P 0.0))"
         "(assert (forall ((x Real)) (=> (P x) (P (+ x 0.5)))))"
         "(assert (forall ((x Real)) (=> (and (P x) (< x 0.0)) false)))", "Problem",
         "  refine ⟨(fun x : Real => 0 ≤ x), ?_, ?_, ?_⟩\n  · exact le_rfl\n"
         "  · intro x hx; exact add_nonneg hx (by norm_num)\n"
         "  · intro x hx hlt; exact (not_lt_of_ge hx) hlt\n"),
        ("horn-witness", "HORN", "(declare-fun P (Real) Bool)(assert (P (/ 0.0 0.0)))"
         "(assert (forall ((x Real)) (=> (and (P x) (distinct x 7.0)) false)))", "Problem",
         "  refine ⟨(fun _ => 7), (fun x => x = 7), ?_, ?_⟩\n"
         "  · simp [SMT.realDiv]\n  · intro x equal different; exact different equal\n"),
        ("horn-sharing", "HORN", "(assert (=> (distinct (/ 0.0 0.0) 7.0) false))"
         "(assert (=> (= (/ 0.0 0.0) 7.0) false))", "¬ Problem",
         "  rintro ⟨d, first, second⟩\n  by_cases h : SMT.realDiv d 0 0 = 7\n"
         "  · exact second h\n  · exact first h\n"),
    ]
    for name, logic, body, target, proof in cases:
        source, output = tmp / f"real-{name}.smt2", tmp / f"real-{name}"
        source.write_text(f"(set-logic {logic}){body}(check-sat)")
        run(source, "--out", output)
        generated = check_generated(lean, output, goal="Problem" if logic == "HORN" else "Refutation")
        if name in ("exact", "horn-linear"):
            assert "realDivZero" not in generated
        completed = output / "Query.lean"
        completed.write_text("import Mathlib.Tactic.NormNum\n" + generated.split("-- Proofs\n", 1)[0]
                             + f"theorem checked : {target} := by\n" + proof)
        check_lean(lean, completed, complete=True)
    # Unused live declarations still affect the quantified domain and import profile.
    for label, body, profile in [
        ("unused", "(declare-const x Real)", "Mathlib.Data.Real.Basic"),
        ("popped", "(push 1)(declare-const x Real)(pop 1)", "Init"),
        ("reset", "(declare-const x Real)(reset)(set-logic ALL)", "Init"),
    ]:
        source, output = tmp / f"real-{label}.smt2", tmp / f"real-{label}"
        source.write_text(f"(set-logic ALL){body}(check-sat)")
        run(source, "--out", output)
        assert check_generated(lean, output).startswith(f"import {profile}\n")
    source = tmp / "later-real-error.smt2"
    source.write_text("(set-logic ALL)(declare-const x Real)(assert (= (/ x 0.0) 1.0))"
                      "(check-sat)(assert (= (^ x 2) 0.0))(check-sat)")
    output = tmp / "later-real-error"
    assert "POW" in run(source, "--out", output, code=1).stderr
    assert not output.exists()
    print("Real semantics passed: 13 exact arithmetic cases, nine completed proofs, SMT/CHC models, and import/scope isolation")


def check_conversions(lean, tmp):
    """Check floor against exact inequalities, and integrality against integer witnesses."""
    for fixture, goal in [(ROOT / "tests/translation/real/conversions.smt2", "Refutation"),
                          (CHC / "conversions.smt2", "Problem")]:
        output = tmp / f"mixed-{goal}"
        run(fixture, "--out", output)
        generated = check_generated(lean, output, goal=goal)
        assert generated.startswith("import Mathlib.Algebra.Order.Archimedean.Real.Basic\n")
    floor_cases = [
        ("0.0", "0"), ("1.7", "1"), ("(- 1.7)", "(- 2)"), ("(- 2.0)", "(- 2)"),
        ("1.99999999999999999999", "1"), ("(- 2.00000000000000000001)", "(- 3)"),
        ("0.00000000000000000001", "0"), ("(- 0.00000000000000000001)", "(- 1)"),
        ("(/ (- 5) 2)", "(- 3)"),
        ("340282366920938463463374607431768211457.5", "340282366920938463463374607431768211457"),
        ("(- 340282366920938463463374607431768211457.5)", "(- 340282366920938463463374607431768211458)"),
    ]
    exact = [f"(= (to_int {real}) {integer})" for real, integer in floor_cases]
    exact += ["(= (to_real (- 340282366920938463463374607431768211457)) "
              "(- 340282366920938463463374607431768211457.0))"]
    cases = [
        ("boundaries", "ALL", "(assert (not (and " + " ".join(exact) + ")))", "Refutation",
         "  intro h\n  apply h\n  norm_num [Int.floor_eq_iff]\n"),
        ("roundtrip", "LIRA", "(declare-const i Int)(assert (distinct (to_int (to_real i)) i))", "Refutation",
         "  intro i h\n  exact h (Int.floor_intCast i)\n"),
        ("integrality", "ALL", "(declare-const x Real)"
         "(assert (distinct (is_int x) (exists ((i Int)) (= x (to_real i)))))", "Refutation",
         "  intro x h\n  apply h\n  apply propext\n  constructor\n"
         "  · intro equal; exact ⟨Int.floor x, equal⟩\n  · rintro ⟨i, rfl⟩; simp\n"),
        ("fraction-not-integral", "ALL", "(assert (is_int 1.5))", "Refutation",
         "  have floor_half : Int.floor (3 / 2 : Real) = 1 := by norm_num [Int.floor_eq_iff]\n"
         "  norm_num [Refutation, floor_half]\n"),
        ("implicit-cast", "ALL", "(declare-const i Int)(assert (= i 3))"
         "(assert (distinct (+ i 0.5) 3.5))", "Refutation",
         "  rintro i ⟨rfl, h⟩\n  apply h\n  norm_num\n"),
        ("zero-floor", "ALL", "(assert (= (to_int (/ 0.0 0.0)) (- 2)))"
         "(assert (not (is_int (/ 0.0 0.0))))", "¬ Refutation",
         "  have floor_neg : Int.floor (- (17 / 10 : Real)) = -2 := by norm_num [Int.floor_eq_iff]\n"
         "  intro h\n  apply h (fun _ => - (17 / 10))\n  norm_num [SMT.realDiv, floor_neg]\n"),
        ("horn-model", "HORN", "(declare-fun P (Int Real) Bool)"
         "(assert (forall ((i Int)) (P i (to_real i))))"
         "(assert (forall ((x Real)) (P (to_int x) x)))"
         "(assert (forall ((i Int) (x Real)) (=> (and (P i x) (distinct i (to_int x))) false)))", "Problem",
         "  refine ⟨(fun i x => i = Int.floor x), ?_, ?_, ?_⟩\n"
         "  · intro i; simp\n  · intro x; rfl\n  · intro i x equal different; exact different equal\n"),
        ("horn-impossible", "HORN", "(declare-fun P (Int) Bool)(assert (P (to_int (- 1.7))))"
         "(assert (forall ((i Int)) (=> (and (P i) (< i (- 1))) false)))", "¬ Problem",
         "  have floor_neg : Int.floor (- (17 / 10 : Real)) = -2 := by norm_num [Int.floor_eq_iff]\n"
         "  rintro ⟨p, fact, safety⟩\n  apply safety _ fact\n  norm_num [floor_neg]\n"),
    ]
    for name, logic, body, target, proof in cases:
        source, output = tmp / f"mixed-{name}.smt2", tmp / f"mixed-{name}"
        source.write_text(f"(set-logic {logic}){body}(check-sat)")
        run(source, "--out", output)
        generated = check_generated(lean, output, goal="Problem" if logic == "HORN" else "Refutation")
        if name == "implicit-cast":
            assert generated.startswith("import Mathlib.Data.Real.Basic\n")
        completed = output / "Query.lean"
        completed.write_text("import Mathlib.Tactic.NormNum\n" + generated.split("-- Proofs\n", 1)[0]
                             + f"theorem checked : {target} := by\n" + proof)
        check_lean(lean, completed, complete=True)
    # A failed command after a valid conversion snapshot must leave no partial file.
    for name, tail, reason in [
        ("sort", "(assert (= (to_real true) 0.0))", "argument"),
        ("unsupported", "(assert (= (^ 2.0 3) 8.0))", "POW"),
    ]:
        source, output = tmp / f"mixed-invalid-{name}.smt2", tmp / f"mixed-invalid-{name}"
        source.write_text("(set-logic ALL)(assert (= (to_int (- 1.7)) (- 2)))(check-sat)" + tail)
        assert reason in run(source, "--out", output, code=1).stderr
        assert not output.exists()
    print("Mixed arithmetic passed: 12 exact boundary cases, eight completed proofs, and SMT/CHC fixtures")


def check_bitvectors(lean, tmp):
    """Standalone core output and completed proofs distinguishing widths and signedness."""
    for fixture, goal in [(ROOT / "tests/translation/bitvec/arithmetic.smt2", "Refutation"),
                          (CHC / "bitvec.smt2", "Problem")]:
        output = tmp / f"bv-{goal}"
        run(fixture, "--out", output)
        generated = check_generated(lean, output, goal=goal)
        assert generated.startswith("import Init\n")
        for helper in (["bvnand", "bvnor", "bvxnor", "bvcomp"] if goal == "Refutation" else ["bvcomp"]):
            assert generated.count(f"def SMT.{helper} ") == 1
    exact = [
        "(= (bvadd #xe #x1 #x2) #x1)", "(= (bvmul #x3 #x5 #x3) #xd)",
        "(= (bvand #xf #x7 #x3) #x3)", "(= (bvor #x1 #x2 #x4) #x7)",
        "(= (bvxor #x1 #x2 #x4) #x7)",
        "(= (bvnand #b1010 #b1100) #b0111)", "(= (bvnor #b1010 #b1100) #b0001)",
        "(= (bvxnor #b1010 #b1100) #b1001)",
        "(= (bvcomp #x0 #x0) #b1)", "(= (bvcomp #x0 #x1) #b0)",
        "(= (bvcomp #b1 #b1) #b1)", "(= #x0001 (_ bv1 16))",
    ]
    for width in [32, 64, 129]:
        modulus = 2 ** width
        exact.extend([
            f"(= (bvadd (_ bv{modulus - 1} {width}) (_ bv1 {width})) (_ bv0 {width}))",
            f"(= (bvneg (_ bv{modulus // 2} {width})) (_ bv{modulus // 2} {width}))",
            f"(= (bvmul (_ bv{modulus // 2} {width}) (_ bv2 {width})) (_ bv0 {width}))",
        ])
    cases = [
        ("exact", "QF_BV", "(assert (not (and " + " ".join(exact) + ")))", "Refutation",
         "  intro h\n  apply h\n  decide\n"),
        ("signedness", "QF_BV", "(declare-const x (_ BitVec 8))"
         "(assert (bvugt x #x00))(assert (bvslt x #x00))", "¬ Refutation",
         "  intro h\n  apply h (255 : BitVec 8)\n  decide\n"),
        ("congruence", "QF_UFBV", "(declare-fun f ((_ BitVec 8)) (_ BitVec 4))"
         "(declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))"
         "(assert (= x y))(assert (distinct (f x) (f y)))", "Refutation",
         "  intro f x y h\n  exact h.2 (congrArg f h.1)\n"),
        ("horn-model", "HORN", "(declare-fun P ((_ BitVec 4)) Bool)(assert (P #x0))"
         "(assert (forall ((x (_ BitVec 4))) (=> (P x) (P (bvadd x #x1)))))"
         "(assert (forall ((x (_ BitVec 4))) (=> (and (P x) (bvult x #x0)) false)))", "Problem",
         "  refine ⟨(fun _ => True), True.intro, (fun _ _ => True.intro), ?_⟩\n"
         "  intro x _ less\n  exact Nat.not_lt_zero x.toNat less\n"),
        ("horn-wrap", "HORN", "(declare-fun P ((_ BitVec 4)) Bool)(assert (P #xf))"
         "(assert (forall ((x (_ BitVec 4))) (=> (P x) (P (bvadd x #x1)))))"
         "(assert (=> (P #x0) false))", "¬ Problem",
         "  rintro ⟨p, fact, step, safety⟩\n  exact safety (step 15 fact)\n"),
    ]
    for name, logic, body, target, proof in cases:
        source, output = tmp / f"bv-{name}.smt2", tmp / f"bv-{name}"
        source.write_text(f"(set-logic {logic}){body}(check-sat)")
        run(source, "--out", output)
        generated = check_generated(lean, output, goal="Problem" if logic == "HORN" else "Refutation")
        assert generated.startswith("import Init\n")
        completed = output / "Query.lean"
        completed.write_text(generated.split("-- Proofs\n", 1)[0]
                             + f"theorem checked : {target} := by\n" + proof)
        check_lean(lean, completed, complete=True)
    # Reject the entire session on a later unsupported operator or stale width alias.
    for name, tail, reason in [
        ("operator", "(assert (= ((_ int_to_bv 4) (^ 2 3)) #x0))", "POW"),
        ("width", "(assert (= (bvadd #x1 #b1) #x2))", "comparable bit-vector"),
        ("scope", "(push 1)(define-sort Byte () (_ BitVec 8))(pop 1)(declare-const x Byte)", "declared"),
        ("reset", "(define-sort Byte () (_ BitVec 8))(reset)(set-logic ALL)(declare-const x Byte)", "declared"),
        ("hidden", "(define-fun ignore ((x (_ BitVec 4))) Bool true)"
         "(assert (ignore ((_ int_to_bv 4) (^ 2 3))))", "POW"),
    ]:
        source, output = tmp / f"bv-invalid-{name}.smt2", tmp / f"bv-invalid-{name}"
        source.write_text("(set-logic ALL)(assert (= #x1 #x1))(check-sat)" + tail)
        assert reason in run(source, "--out", output, code=1).stderr
        assert not output.exists()
    print("Bitvector CLI passed: core-only SMT/CHC output, five completed proofs, and scope/error protection")


def check_bitvector_widths(lean, tmp):
    """Exact widths, standalone output, and completed refutations/Horn models."""
    for fixture, goal in [(ROOT / "tests/translation/bitvec/widths.smt2", "Refutation"),
                          (CHC / "widths.smt2", "Problem")]:
        output = tmp / f"widths-{goal}"
        run(fixture, "--out", output)
        assert check_generated(lean, output, goal=goal).startswith("import Init\n")
    exact = [
        "(= (concat #b1 #b00 #b101) #b100101)",
        "(= ((_ extract 7 4) #xa5) #xa)", "(= ((_ extract 3 0) #xa5) #x5)",
        "(= ((_ extract 7 7) #xa5) #b1)", "(= ((_ extract 0 0) #xa5) #b1)",
        "(= ((_ extract 7 0) #xa5) #xa5)",
        "(= ((_ zero_extend 0) #x8) #x8)", "(= ((_ sign_extend 0) #x8) #x8)",
        "(= ((_ zero_extend 4) #x8) #x08)", "(= ((_ sign_extend 4) #x8) #xf8)",
        "(= ((_ sign_extend 4) #x7) #x07)",
        "(= ((_ sign_extend 7) #b1) #xff)", "(= ((_ zero_extend 7) #b1) #x01)",
        "(= ((_ repeat 1) #xa) #xa)", "(= ((_ repeat 3) #xa) #xaaa)",
        "(= ((_ extract 8 4) ((_ repeat 3) #xa)) #b01010)",
    ]
    for width in [32, 64, 129]:
        half = 2 ** (width - 1)
        exact.extend([
            f"(= ((_ sign_extend 1) (_ bv{half} {width})) (_ bv{3 * half} {width + 1}))",
            f"(= ((_ extract {width} 1) (concat (_ bv{half + 1} {width}) #b0)) (_ bv{half + 1} {width}))",
        ])
    cases = [
        ("exact", "QF_BV", "(assert (not (and " + " ".join(exact) + ")))", "Refutation",
         "  intro h\n  apply h\n  decide\n"),
        ("roundtrip", "QF_BV", "(declare-const hi (_ BitVec 4))(declare-const lo (_ BitVec 3))"
         "(assert (distinct ((_ extract 6 3) (concat hi lo)) hi))", "Refutation",
         "  intro hi lo h\n  exact h BitVec.extractLsb'_append_eq_left\n"),
        ("extension", "QF_BV", "(assert (= ((_ sign_extend 4) #x8) ((_ zero_extend 4) #x8)))", "Refutation",
         "  intro h\n  exact (by decide : (248 : BitVec 8) ≠ 8) h\n"),
        ("horn-model", "HORN", "(declare-fun P ((_ BitVec 8)) Bool)"
         "(assert (P ((_ sign_extend 4) #x8)))(assert (=> (P ((_ zero_extend 4) #x8)) false))", "Problem",
         "  refine ⟨(fun x => x = 248), rfl, ?_⟩\n"
         "  intro h\n  exact (by decide : (8 : BitVec 8) ≠ 248) h\n"),
        ("horn-repeat", "HORN", "(declare-fun P ((_ BitVec 8)) Bool)"
         "(assert (P ((_ repeat 2) #xa)))(assert (=> (P (concat #xa #xa)) false))", "¬ Problem",
         "  rintro ⟨p, fact, safety⟩\n  exact safety fact\n"),
    ]
    for name, logic, body, target, proof in cases:
        source, output = tmp / f"widths-{name}.smt2", tmp / f"widths-{name}"
        source.write_text(f"(set-logic {logic}){body}(check-sat)")
        run(source, "--out", output)
        generated = check_generated(lean, output, goal="Problem" if logic == "HORN" else "Refutation")
        assert generated.startswith("import Init\n")
        completed = output / "Query.lean"
        completed.write_text(generated.split("-- Proofs\n", 1)[0]
                             + f"theorem checked : {target} := by\n" + proof)
        check_lean(lean, completed, complete=True)
    for name, tail, reason in [
        ("slice", "(assert (= ((_ extract 4 0) #xf) #b01111))", "high extract index"),
        ("repeat", "(assert (= ((_ repeat 0) #xf) #xf))", "number of repeats > 0"),
        ("width", "(assert (= ((_ zero_extend 4) #xf) #xf))", "same type"),
        ("hidden", "(define-fun ignore ((x (_ BitVec 8))) Bool true)"
         "(assert (ignore ((_ zero_extend 4) ((_ int_to_bv 4) (^ 2 3)))))", "POW"),
        ("unused", "(define-fun bad () (_ BitVec 8) ((_ zero_extend 4) ((_ int_to_bv 4) (^ 2 3))))", "POW"),
    ]:
        source, output = tmp / f"widths-invalid-{name}.smt2", tmp / f"widths-invalid-{name}"
        source.write_text("(set-logic ALL)(assert (= ((_ repeat 2) #xa) #xaa))(check-sat)" + tail)
        assert reason in run(source, "--out", output, code=1).stderr
        assert not output.exists()
    print("Bitvector widths CLI passed: standalone SMT/CHC output, five completed proofs, and later-error protection")


def check_bitvector_shifts(lean, tmp):
    """Variable shifts, indexed rotations, and huge amounts in standalone output."""
    for fixture, goal in [(ROOT / "tests/translation/bitvec/shifts.smt2", "Refutation"),
                          (CHC / "shifts.smt2", "Problem")]:
        output = tmp / f"shifts-{goal}"
        run(fixture, "--out", output)
        generated = check_generated(lean, output, goal=goal)
        assert generated.startswith("import Init\n")
        for helper in ["bvshl", "bvlshr", "bvashr"]:
            assert generated.count(f"def SMT.{helper} ") == 1
        if goal == "Refutation":
            # Prove the bounded helpers agree with the unbounded core operations
            # for arbitrary widths and operands, not only the numeric samples.
            proofs = ""
            for name, op, zero in [("bvshl", "<<<", "shiftLeft_eq_zero"),
                                   ("bvlshr", ">>>", "ushiftRight_eq_zero")]:
                proofs += f"""
theorem checked_{name} {{w : Nat}} (x y : BitVec w) : SMT.{name} x y = x {op} y.toNat := by
  change x {op} min y.toNat w = x {op} y.toNat
  by_cases h : y.toNat ≤ w
  · simp [Nat.min_eq_left h]
  · have hn : w ≤ y.toNat := by omega
    rw [Nat.min_eq_right hn, BitVec.{zero} (Nat.le_refl w), BitVec.{zero} hn]
"""
            proofs += """
theorem checked_bvashr {w : Nat} (x y : BitVec w) : SMT.bvashr x y = x.sshiftRight y.toNat := by
  change x.sshiftRight (min y.toNat w) = x.sshiftRight y.toNat
  by_cases h : y.toNat ≤ w
  · simp [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega : w ≤ y.toNat)]
    ext i hi
    simp only [BitVec.getElem_sshiftRight]
    simp [show ¬ w + i < w by omega, show ¬ y.toNat + i < w by omega]
"""
            laws = output / "ShiftLaws.lean"
            laws.write_text(generated.split("-- Proofs\n", 1)[0] + proofs)
            check_lean(lean, laws, complete=True)
    exact = [
        "(= (bvshl #x9 #x1) #x2)", "(= (bvlshr #x8 #x1) #x4)",
        "(= (bvashr #x8 #x1) #xc)", "(= (bvashr #x7 #x1) #x3)",
        "(= (bvshl #x1 #x4) #x0)", "(= (bvshl #x1 #x5) #x0)",
        "(= (bvlshr #xf #x4) #x0)", "(= (bvashr #x8 #x4) #xf)",
        "(= ((_ rotate_left 1) #x9) #x3)", "(= ((_ rotate_right 1) #x9) #xc)",
        "(= ((_ rotate_left 4) #x9) #x9)", "(= ((_ rotate_right 5) #x9) #xc)",
        "(= ((_ rotate_left 4294967295) #b1) #b1)",
        "(= (bvshl #b1 #b1) #b0)", "(= (bvashr #b1 #b1) #b1)",
    ]
    for width in [32, 64, 129]:
        maximum, half = 2 ** width - 1, 2 ** (width - 1)
        exact.extend([
            f"(= (bvshl (_ bv1 {width}) (_ bv{maximum} {width})) (_ bv0 {width}))",
            f"(= (bvlshr (_ bv{maximum} {width}) (_ bv{maximum} {width})) (_ bv0 {width}))",
            f"(= (bvashr (_ bv{half} {width}) (_ bv{maximum} {width})) (_ bv{maximum} {width}))",
        ])
    cases = [
        ("exact", "QF_BV", "(assert (not (and " + " ".join(exact) + ")))", "Refutation",
         "  intro h\n  apply h\n  decide\n"),
        ("variable", "QF_BV", "(declare-const x (_ BitVec 4))(declare-const n (_ BitVec 4))"
         "(assert (= n #x0))(assert (distinct (bvshl x n) x))", "Refutation",
         "  intro x n h\n  rcases h with ⟨rfl, h⟩\n  apply h\n  simp [SMT.bvshl]\n"),
        ("signedness", "QF_BV", "(assert (= (bvashr #x8 #x1) (bvlshr #x8 #x1)))", "Refutation",
         "  intro h\n  exact (by decide : (12 : BitVec 4) ≠ 4) h\n"),
        ("horn-model", "HORN", "(declare-fun P ((_ BitVec 4)) Bool)(assert (P #x8))"
         "(assert (forall ((x (_ BitVec 4))) (=> (P x) (P ((_ rotate_left 4) x)))))"
         "(assert (forall ((x (_ BitVec 4))) (=> (and (P x) (distinct (bvshl x #xf) #x0)) false)))", "Problem",
         "  refine ⟨(fun _ => True), True.intro, (fun _ _ => True.intro), ?_⟩\n"
         "  intro x _ h\n  apply h\n  exact BitVec.shiftLeft_eq_zero (by decide)\n"),
        ("horn-rotate", "HORN", "(declare-fun P ((_ BitVec 4)) Bool)(assert (P #x8))"
         "(assert (forall ((x (_ BitVec 4))) (=> (P x) (P ((_ rotate_left 1) x)))))"
         "(assert (=> (P #x1) false))", "¬ Problem",
         "  rintro ⟨p, fact, step, safety⟩\n  exact safety (step 8 fact)\n"),
    ]
    for name, logic, body, target, proof in cases:
        source, output = tmp / f"shifts-{name}.smt2", tmp / f"shifts-{name}"
        source.write_text(f"(set-logic {logic}){body}(check-sat)")
        run(source, "--out", output)
        generated = check_generated(lean, output, goal="Problem" if logic == "HORN" else "Refutation")
        assert generated.startswith("import Init\n")
        completed = output / "Query.lean"
        completed.write_text(generated.split("-- Proofs\n", 1)[0]
                             + f"theorem checked : {target} := by\n" + proof)
        check_lean(lean, completed, complete=True)
    for name, tail, reason in [
        ("width", "(assert (= (bvshl #x1 #b1) #x2))", "comparable bit-vector"),
        ("index", "(assert (= ((_ rotate_left -1) #x8) #x1))", "Negative numerals"),
        ("overflow", "(assert (= ((_ rotate_left 4294967296) #x8) #x8))", "rotation index exceeds"),
        ("unused", "(define-fun bad () (_ BitVec 4) ((_ |rotate_right| 4294967296) #x8))", "rotation index exceeds"),
        ("erased", "(assert (let ((unused ((_ rotate_left 4294967296) #x8))) true))", "rotation index exceeds"),
        ("hidden", "(define-fun ignore ((x (_ BitVec 4))) Bool true)"
         "(assert (ignore (bvshl ((_ int_to_bv 4) (^ 2 3)) #x1)))", "POW"),
    ]:
        source, output = tmp / f"shifts-invalid-{name}.smt2", tmp / f"shifts-invalid-{name}"
        source.write_text("(set-logic ALL)(assert (= (bvshl #x1 #x1) #x2))(check-sat)" + tail)
        assert reason in run(source, "--out", output, code=1).stderr
        assert not output.exists()
    print("Shift CLI passed: three general helper proofs, five completed query proofs, standalone output, and error protection")


def check_bitvector_division(lean, tmp):
    """Standalone output preserves SMT's zero-divisor and signed remainder rules."""
    for fixture, goal in [(ROOT / "tests/translation/bitvec/division.smt2", "Refutation"),
                          (CHC / "bv-division.smt2", "Problem")]:
        output = tmp / f"bv-division-{goal}"
        run(fixture, "--out", output)
        generated = check_generated(lean, output, goal=goal)
        assert generated.startswith("import Init\n")
        for operation in ["smtUDiv", "smtSDiv", "srem", "smod"]:
            assert f".{operation}" in generated
    exact = [
        "(= (bvudiv #xfd #x02) #x7e)", "(= (bvurem #xfd #x02) #x01)",
        "(= (bvsdiv #xfd #x02) #xff)", "(= (bvsrem #xfd #x02) #xff)",
        "(= (bvsmod #xfd #x02) #x01)", "(= (bvsdiv #x03 #xfe) #xff)",
        "(= (bvsrem #x03 #xfe) #x01)", "(= (bvsmod #x03 #xfe) #xff)",
        "(= (bvsdiv #xfd #xfe) #x01)", "(= (bvsrem #xfd #xfe) #xff)",
        "(= (bvsmod #xfd #xfe) #xff)", "(= (bvudiv #x00 #x00) #xff)",
        "(= (bvudiv #xfd #x00) #xff)", "(= (bvurem #xfd #x00) #xfd)",
        "(= (bvsdiv #x00 #x00) #xff)", "(= (bvsdiv #x03 #x00) #xff)",
        "(= (bvsdiv #xfd #x00) #x01)", "(= (bvsrem #xfd #x00) #xfd)",
        "(= (bvsmod #xfd #x00) #xfd)", "(= (bvsdiv #x80 #xff) #x80)",
        "(= (bvsrem #x80 #xff) #x00)", "(= (bvsmod #x80 #xff) #x00)",
    ]
    cases = [
        ("exact", "QF_BV", "(assert (not (and " + " ".join(exact) + ")))", "Refutation",
         "  intro h\n  apply h\n  decide\n"),
        ("remainder-sign", "QF_BV", "(declare-const x (_ BitVec 8))"
         "(assert (= (bvsrem x #x02) #xff))(assert (= (bvsmod x #x02) #x01))", "¬ Refutation",
         "  intro h\n  apply h (253 : BitVec 8)\n  decide\n"),
        ("zero-sign", "QF_BV", "(declare-const x (_ BitVec 8))"
         "(assert (= (bvsdiv x #x00) #x01))(assert (= (bvudiv x #x00) #xff))", "¬ Refutation",
         "  intro h\n  apply h (128 : BitVec 8)\n  decide\n"),
        ("horn-overflow", "HORN", "(declare-fun P ((_ BitVec 4)) Bool)(assert (P #x8))"
         "(assert (forall ((x (_ BitVec 4))) (=> (P x) (P (bvsdiv x #xf)))))"
         "(assert (forall ((x (_ BitVec 4))) (=> (and (P x) (distinct (bvsrem x #xf) #x0)) false)))",
         "Problem", "  refine ⟨(fun x => x = 8), rfl, ?_, ?_⟩\n"
         "  · intro x hx\n    change x = 8 at hx\n    subst x\n    rfl\n"
         "  · intro x hx bad\n    change x = 8 at hx\n    subst x\n    exact bad (by decide)\n"),
        ("horn-modulo", "HORN", "(declare-fun P ((_ BitVec 8)) Bool)"
         "(assert (P (bvsmod #xfd #x02)))(assert (=> (P #x01) false))", "¬ Problem",
         "  rintro ⟨p, fact, safety⟩\n  exact safety fact\n"),
    ]
    for name, logic, body, target, proof in cases:
        source, output = tmp / f"bv-div-{name}.smt2", tmp / f"bv-div-{name}"
        source.write_text(f"(set-logic {logic}){body}(check-sat)")
        run(source, "--out", output)
        generated = check_generated(lean, output, goal="Problem" if logic == "HORN" else "Refutation")
        assert generated.startswith("import Init\n")
        completed = output / "Query.lean"
        completed.write_text(generated.split("-- Proofs\n", 1)[0]
                             + f"theorem checked : {target} := by\n" + proof)
        check_lean(lean, completed, complete=True)
    for name, tail, reason in [
        ("width", "(assert (= (bvsdiv #x1 #b1) #x1))", "comparable bit-vector"),
        ("arity", "(assert (= (bvsmod #x1 #x1 #x1) #x0))", "invalid kind"),
        ("unused", "(define-fun bad () (_ BitVec 4) (bvudiv ((_ int_to_bv 4) (^ 2 3)) #x1))", "POW"),
        ("hidden", "(define-fun ignore ((x (_ BitVec 4))) Bool true)"
         "(assert (ignore (bvsrem ((_ int_to_bv 4) (^ 2 3)) #x1)))", "POW"),
    ]:
        source, output = tmp / f"bv-div-invalid-{name}.smt2", tmp / f"bv-div-invalid-{name}"
        source.write_text("(set-logic ALL)(assert (= (bvudiv #x1 #x0) #xf))(check-sat)" + tail)
        assert reason in run(source, "--out", output, code=1).stderr
        assert not output.exists()
    print("BV division CLI passed: five completed proofs, standalone SMT/CHC output, and later-error protection")


def check_bitvector_conversions(lean, tmp):
    """Wrapping, signedness, and overflow flags through standalone generated code."""
    for fixture, goal in [(ROOT / "tests/translation/bitvec/conversions.smt2", "Refutation"),
                          (CHC / "bv-conversions.smt2", "Problem")]:
        output = tmp / f"bv-conversions-{goal}"
        run(fixture, "--out", output)
        generated = check_generated(lean, output, goal=goal)
        assert generated.startswith("import Init\n")
        for operation in ["ofInt", "toNat", "toInt", "negOverflow", "uaddOverflow",
                          "saddOverflow", "umulOverflow", "smulOverflow"]:
            assert operation in generated
    exact = [
        "(= ((_ int_to_bv 8) (- 1)) #xff)", "(= ((_ int2bv 8) 257) #x01)",
        "(= ((_ int_to_bv 8) (- 257)) #xff)", "(= (ubv_to_int #xff) 255)",
        "(= (bv2nat #x80) 128)", "(= (sbv_to_int #xff) (- 1))",
        "(= (sbv_to_int #x80) (- 128))", "(= (sbv_to_int #x7f) 127)",
        "(= ((_ int_to_bv 1) (- 1)) #b1)", "(= (sbv_to_int #b1) (- 1))",
        "(bvnego #x80)", "(not (bvnego #x7f))",
        "(bvuaddo #xff #x01)", "(not (bvsaddo #xff #x01))",
        "(bvsaddo #x7f #x01)", "(not (bvuaddo #x7f #x01))",
        "(bvumulo #x80 #x02)", "(bvsmulo #x80 #xff)",
        "(not (bvumulo #x0f #x02))", "(not (bvsmulo #x0f #x02))",
        "(= ((_ int_to_bv 129) 680564733841876926926749214863536422913) (_ bv1 129))",
        "(= ((_ int_to_bv 129) (- 680564733841876926926749214863536422913))"
        " (_ bv680564733841876926926749214863536422911 129))",
    ]
    cases = [
        ("exact", "ALL", "(assert (not (and " + " ".join(exact) + ")))", "Refutation",
         "  intro h\n  apply h\n  decide\n"),
        ("round-trip", "ALL", "(declare-const x (_ BitVec 8))"
         "(assert (distinct ((_ int_to_bv 8) (sbv_to_int x)) x))", "Refutation",
         "  intro x bad\n  exact bad BitVec.ofInt_toInt\n"),
        ("signedness", "ALL", "(declare-const x (_ BitVec 8))"
         "(assert (= (ubv_to_int x) 255))(assert (= (sbv_to_int x) (- 1)))", "¬ Refutation",
         "  intro h\n  apply h (255 : BitVec 8)\n  decide\n"),
        ("overflow", "QF_BV", "(declare-const x (_ BitVec 8))"
         "(assert (bvsaddo x #x01))(assert (not (bvuaddo x #x01)))", "¬ Refutation",
         "  intro h\n  apply h (127 : BitVec 8)\n  decide\n"),
        ("horn-model", "HORN", "(declare-fun P ((_ BitVec 8)) Bool)(assert (P #xff))"
         "(assert (forall ((x (_ BitVec 8))) (=> (P x) (P ((_ int_to_bv 8) (ubv_to_int x))))))"
         "(assert (forall ((x (_ BitVec 8))) (=> (and (P x) (< (ubv_to_int x) 0)) false)))",
         "Problem", "  refine ⟨(fun _ => True), True.intro, (fun _ _ => True.intro), ?_⟩\n"
         "  intro x _ bad\n  exact Int.not_lt.mpr (Int.natCast_nonneg x.toNat) bad\n"),
        ("horn-overflow", "HORN", "(declare-fun P ((_ BitVec 8)) Bool)(assert (P #x7f))"
         "(assert (forall ((x (_ BitVec 8))) (=> (and (P x) (bvsaddo x #x01)) false)))",
         "¬ Problem", "  rintro ⟨p, fact, safety⟩\n  exact safety 127 fact (by decide)\n"),
    ]
    for name, logic, body, target, proof in cases:
        source, output = tmp / f"bv-conv-{name}.smt2", tmp / f"bv-conv-{name}"
        source.write_text(f"(set-logic {logic}){body}(check-sat)")
        run(source, "--out", output)
        generated = check_generated(lean, output, goal="Problem" if logic == "HORN" else "Refutation")
        assert generated.startswith("import Init\n")
        completed = output / "Query.lean"
        completed.write_text(generated.split("-- Proofs\n", 1)[0]
                             + f"theorem checked : {target} := by\n" + proof)
        check_lean(lean, completed, complete=True)
    for name, tail, reason in [
        ("width", "(assert (= ((_ int_to_bv 0) 1) #b1))", "expecting bit-width > 0"),
        ("sort", "(assert (= (ubv_to_int 1) 1))", "expecting bit-vector term"),
        ("overflow", "(assert (bvuaddo #x1 #b1))", "comparable bit-vector"),
        ("unused", "(define-fun bad () (_ BitVec 4) ((_ int_to_bv 4) (^ 2 3)))", "POW"),
        ("hidden", "(define-fun ignore ((x (_ BitVec 4))) Bool true)"
         "(assert (ignore ((_ int_to_bv 4) (^ 2 3))))", "POW"),
        ("wide", "(assert (= ((_ int_to_bv 4294967296) 1) #b1))", "conversion width exceeds"),
        ("wide-alias", "(define-fun bad () (_ BitVec 8) ((_ |int2bv| 4294967296) 1))", "conversion width exceeds"),
        ("erased", "(assert (let ((unused ((_ int_to_bv 4294967296) 1))) true))", "conversion width exceeds"),
        ("observation", "(get-value (((_ int2bv 4294967296) 1)))", "conversion width exceeds"),
    ]:
        source, output = tmp / f"bv-conv-invalid-{name}.smt2", tmp / f"bv-conv-invalid-{name}"
        source.write_text("(set-logic ALL)(assert (= ((_ int_to_bv 8) (- 1)) #xff))(check-sat)" + tail)
        assert reason in run(source, "--out", output, code=1).stderr
        assert not output.exists()
    print("BV conversion CLI passed: six completed proofs, standalone SMT/CHC output, and later-error protection")


def check_arrays_basic(lean, tmp):
    """Check array laws through complete proofs and an explicit satisfying model."""
    source, output = tmp / "arrays-basic.smt2", tmp / "arrays-basic"
    source.write_text("""(set-logic ALL)
(define-sort Arr (I E) (Array I E))
(declare-const a (Arr Int Int))
(declare-const b (Array Int Int))
(declare-const i Int)
(declare-const p Bool)
(declare-fun f ((Array Int Int)) (Array Int Int))
(define-fun put ((a (Array Int Int)) (i Int)) (Array Int Int) (store a i (+ i 1)))
(assert (= (select (put a i) i) (+ i 1)))
(assert (= (ite p (f a) b) (ite p (f a) b)))
(assert (distinct a b))
(assert (forall ((k Int)) (= (select a k) (select b k))))
(check-sat)
""")
    run(source, "--out", output)
    generated = check_generated(lean, output)
    assert generated.startswith("import Init\n")
    assert generated.count("def SMT.arrayLaws ") == 1
    assert "Nonempty" in generated and "axiom " not in generated
    cases = [
        ("read-write", "(declare-const a (Array Int Int))(declare-const i Int)"
         "(declare-const v Int)(assert (distinct (select (store a i v) i) v))", "Refutation",
         "  intro A read write a i v laws bad\n  exact bad (laws.2.1 a i v)\n"),
        ("other-index", "(declare-const a (Array Int Int))(declare-const i Int)"
         "(declare-const j Int)(declare-const v Int)(assert (distinct i j))"
         "(assert (distinct (select (store a i v) j) (select a j)))", "Refutation",
         "  intro A read write a i j v laws h\n  exact h.2 (laws.2.2.1 a i j v h.1)\n"),
        ("extensional", "(declare-const a (Array Int Int))(declare-const b (Array Int Int))"
         "(assert (forall ((i Int)) (= (select a i) (select b i))))"
         "(assert (distinct a b))", "Refutation",
         "  intro A read write a b laws h\n  exact h.2 (laws.2.2.2 a b h.1)\n"),
        ("model", "(declare-const a (Array Int Int))(assert (= (select a 4) 0))", "¬ Refutation",
         "  let write : (Int → Int) → Int → Int → (Int → Int) :=\n"
         "    fun a i v j => if j = i then v else a j\n"
         "  have laws : SMT.arrayLaws Int Int (Int → Int) (fun a i => a i) write := by\n"
         "    refine ⟨⟨fun _ => 0⟩, ?_, ?_, ?_⟩\n"
         "    · intro a i v; simp [write]\n"
         "    · intro a i j v different; simp [write, Ne.symm different]\n"
         "    · intro a b same; exact funext same\n"
         "  intro refute\n  exact refute (Int → Int) (fun a i => a i) write (fun _ => 0) laws rfl\n"),
    ]
    for name, body, target, proof in cases:
        source, output = tmp / f"arrays-{name}.smt2", tmp / f"arrays-{name}"
        source.write_text(f"(set-logic ALL){body}(check-sat)")
        run(source, "--out", output)
        generated = check_generated(lean, output)
        completed = output / "Query.lean"
        completed.write_text(generated.split("-- Proofs\n", 1)[0]
                             + f"theorem checked : {target} := by\n" + proof
                             + "\n#print axioms checked\n")
        assert "sorryAx" not in check_lean(lean, completed, complete=True)

    source, output = tmp / "arrays-session.smt2", tmp / "arrays-session"
    source.write_text("""(set-logic ALL)
(declare-const a (Array Int Int))
(assert (= (select a 0) 1))
(check-sat)
(push 1)
(declare-const b (Array Int Bool))
(assert (select b 0))
(check-sat)
(pop 1)
(check-sat)
(reset-assertions)
(declare-sort S 0)
(declare-const a (Array S Int))
(check-sat)
(reset)
(set-logic ALL)
(declare-const a (Array Bool Int))
(assert (= (select a true) 0))
(check-sat)
""")
    run(source, "--out", output)
    generated = check_generated(lean, output, count=5)
    assert generated.count("def SMT.arrayLaws ") == 1
    query = output / "Query.lean"
    saved = generated + "\n-- Reviewed array proofs.\n"
    query.write_text(saved)
    run(source, "--out", output, code=1)
    assert query.read_text() == saved
    for name, tail in [
        ("index", "(assert (= (select a true) 0))"),
        ("value", "(assert (= (store a 0 true) a))"),
        ("element-sort", "(declare-const unsupported (Array Int String))"),
        ("popped", "(push 1)(declare-const b (Array Int Int))(pop 1)(assert (= a b))"),
    ]:
        source, output = tmp / f"arrays-bad-{name}.smt2", tmp / f"arrays-bad-{name}"
        source.write_text("(set-logic ALL)(declare-const a (Array Int Int))(check-sat)" + tail)
        run(source, "--out", output, code=1)
        assert not output.exists()
    print("Array CLI passed: four completed proofs, standalone output, five snapshots, and error protection")


def check_arrays_extended(lean, tmp):
    """Recheck quantified/nested arrays, constant arrays, and Horn model existence."""
    generated_fixtures = {}
    for name, fixture, goal in [
        ("nested", ROOT / "tests/translation/arrays/nested.smt2", "Refutation"),
        ("constants", ROOT / "tests/translation/arrays/constants.smt2", "Refutation"),
        ("horn", CHC / "arrays.smt2", "Problem"),
        ("horn-constants", CHC / "array-constants.smt2", "Problem"),
    ]:
        output = tmp / f"arrays-extended-{name}"
        run(fixture, "--out", output)
        generated = check_generated(lean, output, goal=goal)
        assert generated.count("def SMT.arrayLaws ") == 1
        assert generated.count("def SMT.constArrayLaw ") == (1 if "constants" in name else 0)
        generated_fixtures[name] = generated

    cases = [
        ("constant-read", "(declare-const i Int)"
         "(assert (distinct (select ((as const (Array Int Int)) 0) i) 0))",
         "  intro A read write const i laws bad\n  exact bad (laws.2 0 i)\n"),
        ("nested-update", "(declare-const a (Array Int (Array Int Int)))"
         "(declare-const row (Array Int Int))(declare-const i Int)(declare-const j Int)"
         "(assert (distinct (select (select (store a i row) i) j) (select row j)))",
         "  intro A readA writeA B readB writeB a row i j laws bad\n"
         "  exact bad (congrArg (fun r => readA r j) (laws.2.2.1 a i row))\n"),
    ]
    for name, body, proof in cases:
        source, output = tmp / f"arrays-{name}.smt2", tmp / f"arrays-{name}"
        source.write_text(f"(set-logic ALL){body}(check-sat)")
        run(source, "--out", output)
        generated = check_generated(lean, output)
        completed = output / "Query.lean"
        completed.write_text(generated.split("-- Proofs\n", 1)[0]
                             + "theorem checked : Refutation := by\n" + proof
                             + "\n#print axioms checked\n")
        assert "sorryAx" not in check_lean(lean, completed, complete=True)

    completed = tmp / "arrays-extended-horn-constants" / "Query.lean"
    completed.write_text(generated_fixtures["horn-constants"].split("-- Proofs\n", 1)[0] + """
theorem checked : Problem := by
  let write : (Int → Int) → Int → Int → (Int → Int) :=
    fun a i v j => if j = i then v else a j
  have laws : SMT.arrayLaws Int Int (Int → Int) (fun a i => a i) write := by
    refine ⟨⟨fun _ => 0⟩, ?_, ?_, ?_⟩
    · intro a i v; simp [write]
    · intro a i j v different; simp [write, Ne.symm different]
    · intro a b same; exact funext same
  refine ⟨Int → Int, (fun a i => a i), write, (fun v _ => v),
    (fun a => a 0 = 0), laws, ?_, rfl, ?_, ?_⟩
  · intro v i; rfl
  · intro a _; simp [write]
  · intro a same different; exact different same

#print axioms checked
""")
    assert "sorryAx" not in check_lean(lean, completed, complete=True)

    source, output = tmp / "arrays-constant-scopes.smt2", tmp / "arrays-constant-scopes"
    source.write_text("""(set-logic ALL)
(check-sat)
(push 1)
(define-fun unused ((i Int)) Bool (let ((erased ((as const (Array Int Int)) 0))) true))
(check-sat)
(pop 1)
(check-sat)
(assert (let ((erased ((as const (Array Int Int)) 0))) true))
(check-sat)
(reset-assertions)
(check-sat)
(define-fun zero () (Array Int Int) ((as const (Array Int Int)) 0))
(check-sat)
(reset)
(set-logic ALL)
(check-sat)
""")
    run(source, "--out", output)
    generated = check_generated(lean, output, count=7)
    assert generated.count("def SMT.constArrayLaw ") == 1
    for number in range(1, 8):
        body = generated.split(f"def Refutation_{number} : Prop :=\n", 1)[1]
        body = body.split("-- Source:", 1)[0].split("-- Proofs", 1)[0]
        assert ("SMT.constArrayLaw" in body) == (number in [2, 4, 6]), (number, body)
    for name, tail in [
        ("symbolic", "(declare-const v Int)(assert (= (select ((as const (Array Int Int)) v) 0) v))"),
        ("local", "(assert (= (select (let ((v 0)) ((as const (Array Int Int)) v)) 0) 0))"),
        ("named", "(assert (= (select ((as const (Array Int Int)) (! 0 :named payload)) 0) 0))"),
        ("wrong-index", "(assert (= (select ((as const (Array Int Int)) 0) true) 0))"),
        ("string-sort", "(declare-const unsupported (Array Int (Array Int String)))"),
    ]:
        source, output = tmp / f"arrays-extended-bad-{name}.smt2", tmp / f"arrays-extended-bad-{name}"
        source.write_text("(set-logic ALL)(assert (= (select ((as const (Array Int Int)) 0) 0) 0))"
                          "(check-sat)" + tail)
        result = run(source, "--out", output, code=1)
        if name == "local":
            assert "self-contained native value" in result.stderr, result.stderr
        assert not output.exists()
    source, output = tmp / "arrays-global-name.smt2", tmp / "arrays-global-name"
    source.write_text("""(set-option :global-declarations true)
(set-logic ALL)
(check-sat)
(push 1)
(assert (! (let ((erased ((as const (Array Int Int)) 0))) true) :named p))
(pop 1)
(assert (forall ((a (Array Int Int))) (exists ((i Int)) (distinct (select a i) 0))))
(check-sat-assuming (p))
""")
    assert "global :named terms are unsupported" in run(source, "--out", output, code=1).stderr
    assert not output.exists()
    print("Extended array CLI passed: four fixtures, three completed proofs, seven scope snapshots, and rejected payloads")


def main():
    prefix = subprocess.check_output(["lean", "--print-prefix"], cwd=ROOT, text=True).strip()
    lean = Path(prefix) / "bin/lean"
    expected = {
        "contradiction": (FIXTURES / "expected/Query.lean").read_text(),
        "bounds": (INTEGERS / "expected/Query.lean").read_text(),
        "congruence": (FUNCTIONS / "expected/Query.lean").read_text(),
        "quantified": (QUANTIFIERS / "expected/Query.lean").read_text(),
        "lh_sum_rec": (CHC / "expected/Query.lean").read_text(),
    }
    help_text = run("--help").stdout
    assert all(word in help_text for word in ["Usage:", "HORN", "Problem", "Refutation"])
    for args in [(), ("--unknown",), ("input.smt2",),
                 ("input.smt2", "--out", ""), ("input.smt2", "--out", "--help")]:
        run(*args, code=2)

    with tempfile.TemporaryDirectory(prefix="smt2lean cli ") as temporary:
        tmp = Path(temporary)
        for fixture, goal, count in [("smt", "Refutation", 8), ("chc", "Problem", 6), ("assuming", "Refutation", 6), ("resets", "Refutation", 7), ("sorts", "Refutation", 8)]:
            output = tmp / f"session-{fixture}"
            run(SESSIONS / f"{fixture}.smt2", "--out", output)
            generated = check_generated(lean, output, goal=goal, count=count)
            if fixture == "smt":
                assert generated.count("def SMT.xor ") == generated.count("def SMT.distinct3.{") == 1
            query = output / "Query.lean"
            edited = generated + "\n-- User session proof work.\n"
            query.write_text(edited)
            run(SESSIONS / f"{fixture}.smt2", "--out", output, code=1)
            assert query.read_text() == edited

        check_uninterpreted_sorts(lean, tmp)
        check_integer_division(lean, tmp)
        check_reals(lean, tmp)
        check_conversions(lean, tmp)
        check_bitvectors(lean, tmp)
        check_bitvector_widths(lean, tmp)
        check_bitvector_shifts(lean, tmp)
        check_bitvector_division(lean, tmp)
        check_bitvector_conversions(lean, tmp)
        check_arrays_basic(lean, tmp)
        check_arrays_extended(lean, tmp)

        for logic, goal in [("ALL", "Refutation"), ("HORN", "Problem")]:
            for name, body, count in [
                ("empty", "(check-sat)\n(check-sat)\n(push 1)", 2),
                ("single", "(push 1)\n(assert false)\n(pop 1)\n(check-sat)", 1),
                ("configured", "(assert false)\n(check-sat)\n"
                 "(set-option :print-success false)\n(set-info :status unknown)\n(check-sat)", 2),
            ]:
                source, output = tmp / f"session-{logic}-{name}.smt2", tmp / f"session-{logic}-{name}"
                source.write_text(f"(set-logic {logic})\n" + body)
                result = run(source, "--out", output)
                assert "success" not in result.stdout and "unsat" not in result.stdout
                generated = check_generated(lean, output, goal=goal, count=count)
                if name == "single":
                    expected_body = "True → False" if logic == "ALL" else "True"
                    assert f"def {goal} : Prop :=\n  {expected_body}\n" in generated

        # A later failure must leave no output, even after reconstructing query 1.
        for name, text, reason in [
            ("underflow", "(set-logic ALL)\n(check-sat)\n(pop 1)", "exceeds active scope depth"),
            ("operator", "(set-logic ALL)\n(check-sat)\n(assert (= (^ 1 0) 0))", "unsupported operator"),
            ("popped-name", "(set-logic ALL)\n(push 1)\n(declare-const p Bool)\n"
             "(assert p)\n(check-sat)\n(pop 1)\n(assert p)", "not declared"),
            ("clause", "(set-logic HORN)\n(declare-fun P (Int) Bool)\n(assert (P 0))\n"
             "(check-sat)\n(assert (=> (not (P 0)) false))\n(check-sat)",
             "CHC relation inside a theory guard"),
            ("declaration", "(set-logic HORN)\n(check-sat)\n(declare-const x Int)\n(check-sat)",
             "unsupported CHC declaration"),
        ]:
            source, output = tmp / f"session-bad-{name}.smt2", tmp / f"session-bad-{name}"
            source.write_text(text)
            result = run(source, "--out", output, code=1)
            assert "query 2:" in result.stderr and reason in result.stderr, result.stderr
            assert not output.exists()

        inputs = [FIXTURES / f"{name}.smt2" for name in ["contradiction", "connectives", "empty", "options"]]
        inputs += [INTEGERS / f"{name}.smt2" for name in ["literals", "arithmetic", "bounds"]]
        inputs += [FUNCTIONS / f"{name}.smt2" for name in ["applications", "congruence"]]
        inputs += [QUANTIFIERS / f"{name}.smt2" for name in ["scopes", "quantified", "hints"]]
        inputs += [BINDINGS / name for name in ["simultaneous.smt2", "definitions.smt2", "named.smt2"]]
        inputs += [ROOT / "tests/translation/sorts/uninterpreted.smt2"]
        for fixture in inputs:
            name = fixture.stem
            output = tmp / name
            result = run(fixture, "--out", output)
            assert "Proof unfinished" in result.stdout
            source = check_generated(lean, output)
            if name == "options":
                assert without_sources(source) == without_sources(expected["contradiction"])
                assert "success" not in result.stdout and "unsat" not in result.stdout
            if name == "named":
                assert '(:named "positive")' in source and '(:named "same body")' in source
                assert '(:named "line\\nname", "also")' in source
                assert "\nname" not in source
            if name in expected:
                assert source == expected[name], (f"{name} output changed", source)
            if name in ["literals", "arithmetic"]:
                assert "340282366920938463463374607431768211457" in source
            query = output / "Query.lean"
            edited = source + "\n-- User proof work.\n"
            query.write_text(edited)
            result = run(fixture, "--out", output, code=1)
            assert "output already exists" in result.stderr
            assert query.read_text() == edited

        for fixture, proof in [
            (FIXTURES / "contradiction.smt2", "  intro p h\n  exact h.2 h.1\n"),
            (INTEGERS / "bounds.smt2", "  intro x h\n  exact Int.not_lt_of_ge h.1 h.2\n"),
            (FUNCTIONS / "congruence.smt2", "  intro f x y h\n  exact h.2 (congrArg f h.1)\n"),
            (QUANTIFIERS / "quantified.smt2", "  intro P h\n  exact h.2.elim (fun x hx => hx (h.1 x))\n"),
        ]:
            name = fixture.stem
            for status in ["sat", "unsat", "unknown"]:
                source, output = tmp / f"{name}-{status}.smt2", tmp / f"{name}-{status}"
                source.write_text(SOLVER_OPTIONS + f"(set-info :status {status})\n" + fixture.read_text())
                run(source, "--out", output)
                generated = check_generated(lean, output)
                assert without_sources(generated) == without_sources(expected[name]), f"{name}: {status} changed the target"

            # Replace the Proofs section exactly as in the README.
            completed = tmp / name / "Query.lean"
            statements = completed.read_text().split("-- Proofs\n", 1)[0]
            finished = statements + "-- Proofs\n\ntheorem refutation : Refutation := by\n" + proof
            completed.write_text(finished + "\n#print axioms refutation\n")
            axioms = check_lean(lean, completed, complete=True)
            assert "sorryAx" not in axioms, axioms
            if name == "bounds":
                # This core integer-order lemma uses propositional extensionality.
                assert "depends on axioms: [propext]" in axioms
            else:
                assert "does not depend on any axioms" in axioms
            saved = completed.read_text()
            run(fixture, "--out", completed.parent, code=1)
            assert completed.read_text() == saved

        # Quantifier hints must leave the entire emitted proposition unchanged.
        source, output = tmp / "quantified-hinted.smt2", tmp / "quantified-hinted"
        text = (QUANTIFIERS / "quantified.smt2").read_text()
        text = text.replace("(forall ((x Int)) (P x))",
                            "(forall ((x Int)) (! (P x) :pattern ((P x)) :qid universal))")
        text = text.replace("(exists ((x Int)) (not (P x)))",
                            "(exists ((x Int)) (! (not (P x)) :no-pattern (P x) :qid witness))")
        source.write_text(text)
        run(source, "--out", output)
        generated = check_generated(lean, output)
        assert without_sources(generated) == without_sources(expected["quantified"])

        missing_output = tmp / "missing-output"
        run(tmp / "missing.smt2", "--out", missing_output, code=1)
        assert not missing_output.exists()

        horn = ROOT / "tests/chc/lh_sum_rec.smt2"
        horn_output = tmp / "horn"
        run(horn, "--out", horn_output)
        horn_source = check_generated(lean, horn_output, goal="Problem")
        assert horn_source == expected["lh_sum_rec"], "lh_sum_rec output changed"
        assert horn_source.count("(clause ") == 3
        horn_text = horn.read_text()
        for status in [None, "unsat", "unknown"]:
            source, output = tmp / f"horn-{status}.smt2", tmp / f"horn-{status}"
            metadata = "" if status is None else f"(set-info :status {status})"
            source.write_text(SOLVER_OPTIONS + horn_text.replace("(set-info :status sat)", metadata))
            run(source, "--out", output)
            generated = check_generated(lean, output, goal="Problem")
            assert without_sources(generated) == without_sources(horn_source), status

        output = tmp / "combined-chc"
        run(CHC / "clauses.smt2", "--out", output)
        combined = check_generated(lean, output, goal="Problem")
        assert combined.count("(clause ") == 16

        output = tmp / "definitions-chc"
        run(CHC / "definitions.smt2", "--out", output)
        generated = check_generated(lean, output, goal="Problem")
        assert generated.count("(clause ") == 3
        assert all(f'(:named "{name}")' in generated for name in ["entry clause", "step", "safety"])

        source, output = tmp / "hinted-chc.smt2", tmp / "hinted-chc"
        text = (CHC / "definitions.smt2").read_text()
        text = text.replace("(=> |entry clause| (rule x b))",
                            "(! (=> |entry clause| (rule x b)) :pattern ((P x) (R x b)) "
                            ":no-pattern (P (^ x 2)) :qid step)")
        text = text.replace("(=> (bad x b) false)",
                            "(! (=> (bad x b) false) :pattern ((R x b)) :qid safety)")
        source.write_text(text)
        run(source, "--out", output)
        hinted = check_generated(lean, output, goal="Problem")
        assert without_sources(hinted) == without_sources(generated)

        query = horn_output / "Query.lean"
        edited = horn_source + "\n-- User CHC proof work.\n"
        query.write_text(edited)
        result = run(horn, "--out", horn_output, code=1)
        assert "output already exists" in result.stderr and query.read_text() == edited

        # Equivalent parsed logic with comments/whitespace; no clauses means True.
        source, output = tmp / "empty-horn.smt2", tmp / "empty-horn"
        source.write_text("(set-logic ; parsed as HORN\n HORN)\n(check-sat)")
        run(source, "--out", output)
        empty_horn = check_generated(lean, output, goal="Problem")
        assert "def Problem : Prop :=\n  True\n" in empty_horn

        # The same assertions follow the SMT path without an explicit HORN logic.
        smt_source = None
        for logic in ["(set-logic ALL)", ""]:
            name = "horn-as-smt" if logic else "horn-no-logic"
            source, output = tmp / f"{name}.smt2", tmp / name
            source.write_text(horn_text.replace("(set-logic HORN)", logic))
            run(source, "--out", output)
            generated = check_generated(lean, output)
            if smt_source is not None:
                assert without_sources(generated) == without_sources(smt_source)
            smt_source = generated

        # HORN text in comments, names, and metadata must never select CHC mode.
        source, output = tmp / "horn-text.smt2", tmp / "horn-text"
        source.write_text('''; (set-logic HORN)
(set-info :source "(set-logic HORN)")
(set-logic ALL)
(declare-const |(set-logic HORN)| Int)
(assert (= |(set-logic HORN)| 0))
(check-sat)
(set-info :status sat)
''')
        run(source, "--out", output)
        check_generated(lean, output)

        horn_prefix = "(set-logic HORN)\n(declare-fun P (Int) Bool)\n(assert (P 0))\n"
        for name, text, location, reason in [
            ("later-clause", horn_prefix +
             "(assert (forall ((x Int)) (=> (not (P x)) false)))\n(check-sat)",
             "4:1: query 1: command 4: clause 2:", "CHC relation inside a theory guard"),
            ("later-operator", horn_prefix +
             "(assert (forall ((x Int)) (=> (= (^ x 2) 0) (P x))))\n(check-sat)",
             "4:1: query 1: command 4: clause 2:", "unsupported operator"),
            ("let-operator", horn_prefix +
             "(assert (forall ((x Int)) (let ((half (^ x 2))) (=> (= half 0) (P x)))))\n(check-sat)",
             "4:1: query 1: command 4: clause 2:", "unsupported operator"),
            ("let-relation", horn_prefix +
             "(assert (forall ((x Int)) (let ((hidden (not (P x)))) (=> hidden (P x)))))\n(check-sat)",
             "4:1: query 1: command 4: clause 2:", "CHC relation inside a theory guard"),
            ("defined-negative-relation", horn_prefix +
             "(define-fun neg ((x Int)) Bool (not (P x)))\n"
             "(assert (forall ((x Int)) (=> (neg x) false)))\n(check-sat)",
             "5:1: query 1: command 5: clause 2:", "CHC relation inside a theory guard"),
            ("defined-quantifier", horn_prefix +
             "(define-fun someP () Bool (exists ((x Int)) (P x)))\n"
             "(assert (=> someP false))\n(check-sat)",
             "5:1: query 1: command 5: clause 2:", "quantifier"),
            ("unused-definition", horn_prefix +
             "(define-fun bad () Int (^ 1 0))\n(check-sat)",
             "4:1: query 1: command 4:", "POW"),
            ("named-clause", horn_prefix +
             '(assert (! (forall ((x Int)) (=> (not (P x)) false)) :named |bad clause|))\n(check-sat)',
             '4:1: query 1: command 4 (:named "bad clause"): clause 2:', "CHC relation inside a theory guard"),
            ("hinted-clause", horn_prefix +
             '(assert (forall ((x Int)) (! (=> (not (P x)) false) :pattern ((P x)) :qid bad)))\n(check-sat)',
             "4:1: query 1: command 4: clause 2:", "CHC relation inside a theory guard"),
            ("global-int", "(set-logic HORN)\n(declare-const x Int)\n(check-sat)",
             "2:1: query 1: command 2:", "unsupported CHC declaration"),
            ("malformed-tail", horn_prefix + "(check-sat)\n(assert",
             "5:8: query 2: command 5:", "unterminated command"),
            ("missing-check", horn_prefix, "4:1: query 1: command 4:", "expected at least one check-sat"),
        ]:
            source, output = tmp / f"horn-{name}.smt2", tmp / f"horn-{name}"
            source.write_text(text)
            result = run(source, "--out", output, code=1)
            # cvc5 renders its diagnostic message as an escaped string.
            escaped_location = location.replace('"', '\\"')
            assert f"{source}:{escaped_location}" in result.stderr, result.stderr
            assert reason in result.stderr, result.stderr
            assert not output.exists()

        # Bad configuration rejects the whole query, with locations, in either mode.
        for logic in ["ALL", "HORN"]:
            for number, (command, reason) in enumerate([
                ('(set-option :produce-models "true")', "invalid value for :produce-models"),
                ("(set-option :random-seed -1)", "invalid value for :random-seed"),
                ("(set-option :global-declarations true)", "must be set before"),
                ("(set-option :unknown false)", "unsupported solver option"),
                ("(set-info :unknown true)", "unsupported metadata"),
                ("(get-proof)", "requires a preceding check"),
                ("(get-model)", "requires a preceding check"),
                ("(get-unsat-core)", "requires a preceding check"),
            ]):
                source, output = tmp / f"config-{logic}-{number}.smt2", tmp / f"config-{logic}-{number}"
                source.write_text(f"(set-logic {logic})\n(assert false)\n{command}\n(check-sat)")
                result = run(source, "--out", output, code=1)
                context = "query 1: " if logic == "HORN" else ""
                assert f"{source}:3:1: {context}command 3:" in result.stderr, result.stderr
                assert reason in result.stderr and not output.exists(), result.stderr
            for suffix in ['(echo "ignored")']:
                source, output = tmp / f"config-tail-{logic}.smt2", tmp / f"config-tail-{logic}"
                source.write_text(SOLVER_OPTIONS + f"(set-logic {logic})\n(assert false)\n(check-sat)\n" + suffix)
                result = run(source, "--out", output, code=1)
                assert "unsupported command" in result.stderr and not output.exists(), result.stderr

        check_resets(lean, tmp)

        for logic, literal in [("ALL", "true"), ("ALL", "(and p p)"), ("ALL", "missing"),
                               ("HORN", "true")]:
            source, output = tmp / "bad-assumption.smt2", tmp / "bad-assumption"
            source.write_text(f"(set-logic {logic})(declare-const p Bool)(check-sat)(check-sat-assuming ({literal}))")
            run(source, "--out", output, code=1)
            assert not output.exists()
        source, output = tmp / "horn-assuming.smt2", tmp / "horn-assuming"
        source.write_text("(set-logic HORN)(declare-const p Bool)(check-sat-assuming (p (not p)))(check-sat)")
        run(source, "--out", output)
        text = check_generated(lean, output, goal="Problem", count=2)
        assert "check-sat-assuming," in text and "assumption 2" in text

        invalid = [
            "(set-logic QF_S)\n(check-sat)",
            "(set-logic QF_UF)\n(check-sat)\n(pop 1)",
            "(set-logic QF_UF)\n(check-sat)\n(assert",
            "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (= (^ x 0) 0))\n(check-sat)",
            "(set-logic ALL)\n(declare-fun P (String) Bool)\n(check-sat)",
            "(set-logic QF_UFLIA)\n(declare-fun f (Int Int) Int)\n(assert (= (f 1) 0))\n(check-sat)",
            "(set-logic QF_UFLIA)\n(declare-fun f (Int) Int)\n(assert (= (f true) 0))\n(check-sat)",
            "(set-logic ALL)\n(assert (forall ((x String)) true))\n(check-sat)",
            "(set-logic QF_LIA)\n(assert (forall ((x Int)) (> x 0)))\n(check-sat)",
            "(set-logic ALL)\n(assert (exists ((p Bool)) (= (ite p 1 (^ 1 0)) 1)))\n(check-sat)",
            "(set-logic ALL)\n(assert (ite 1 true false))\n(check-sat)",
            "(set-logic ALL)\n(assert (ite true false 1))\n(check-sat)",
            "(set-logic QF_LIA)\n(assert (let ((x 1) (y x)) (= y 1)))\n(check-sat)",
            "(set-logic QF_UF)\n(assert (let ((p true) (q p)) q))\n(check-sat)",
            "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (let ((half (^ x 2))) (let ((copy half)) (= copy 0))))\n(check-sat)",
            "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (let ((next (+ x 1))) (= (^ next 2) 0)))\n(check-sat)",
            "(set-logic UFLIA)\n(declare-fun P (Int) Bool)\n(assert (forall ((x Int)) (! (P x) :weight 5)))\n(check-sat)",
        ]
        for index, text in enumerate(invalid):
            source, output = tmp / f"invalid-{index}.smt2", tmp / f"invalid-{index}"
            source.write_text(text)
            result = run(source, "--out", output, code=1)
            assert re.search(re.escape(str(source)) + r":\d+:\d+: (?:query \d+: )?command ", result.stderr), result.stderr
            assert not output.exists()

        # Quoted names and doubled quotes cannot move source boundaries. Keep CRLF bytes.
        source, output = tmp / "locations\n-- name.smt2", tmp / "locations"
        text = ('; λ ignored )\r\n(set-logic QF_UF)\r\n'
                '(set-info :source "(; ""quoted"")")\r\n'
                '(declare-const |p (;)| Bool)\r\n'
                '(assert\r\n  |p (;)|)\r\n(check-sat)')
        source.write_bytes(text.encode())
        run(source, "--out", output)
        generated = check_generated(lean, output)
        assert '\\n-- name.smt2":5:1-6:11 (assertion 1, command 4)' in generated
        # Move the same assertion and ensure only provenance changes.
        shifted, shifted_output = tmp / "shifted.smt2", tmp / "shifted"
        shifted.write_bytes(('\n\n' + text).encode())
        run(shifted, "--out", shifted_output)
        shifted_code = check_generated(lean, shifted_output)
        assert '":7:1-8:11 (assertion 1, command 4)' in shifted_code
        assert without_sources(shifted_code) == without_sources(generated)
        for name, text, location, reason in [
            ("multiline", "; λ\n(set-logic ALL)\n  (assert\n    (= (^ 1 0) 0))\n(check-sat)",
             "3:3: command 2:", "unsupported operator"),
            ("definition-source", "; λ\n(set-logic ALL)\n  (define-fun bad ((x Int)) Int\n    (^ x 2))\n(check-sat)",
             "3:3: command 2:", "POW"),
            ("named-source", '(set-logic ALL)\n  (assert (! (= (^ 1 0) 0) :named |bad body|))\n(check-sat)',
             '2:3: command 2 (:named "bad body"):', "POW"),
            ("unused-named-source", '(set-logic ALL)\n  (assert (let ((ignored (! (^ 1 0) :named |unused body|))) true))\n(check-sat)',
             '2:3: command 2 (:named "unused body"):', "POW"),
            ("alias-source", "(set-logic ALL)\n  (define-sort Bad () String)\n(check-sat)",
             "2:3: command 2:", "unsupported sort alias"),
            ("bad-string", '(set-logic QF_UF)\n(set-info :source "unfinished',
             "2:30: command 2:", "unterminated string"),
            ("extra-close", "(set-logic QF_UF)\n(check-sat)\n  )",
             "3:3: query 2: command 3:", "expected '('"),
        ]:
            source, output = tmp / f"{name}.smt2", tmp / name
            source.write_text(text)
            result = run(source, "--out", output, code=1)
            # cvc5 renders its diagnostic message as an escaped string.
            escaped_location = location.replace('"', '\\"')
            assert f"{source}:{escaped_location}" in result.stderr, result.stderr
            assert reason in result.stderr and not output.exists(), result.stderr

        # Existing empty directories, files, and symlinks must also be refused.
        empty_dir, occupied_file, link = tmp / "existing", tmp / "file", tmp / "link"
        empty_dir.mkdir()
        occupied_file.write_text("keep")
        link.symlink_to(tmp / "absent")
        for output in [empty_dir, occupied_file, link]:
            run(FIXTURES / "contradiction.smt2", "--out", output, code=1)
        assert not list(empty_dir.iterdir())
        assert occupied_file.read_text() == "keep" and link.is_symlink()

        output = tmp / "missing-parent" / "output"
        run(FIXTURES / "contradiction.smt2", "--out", output, code=1)
        assert not output.exists()

    print("CLI passed: generation, exit codes, diagnostics, and output protection")
    print("Demo passed: standalone SMT/CHC translations, source locations, and completed proofs")
    print("Sessions passed: numbered SMT/CHC goals, standalone statements, later failures, and proof protection")


if __name__ == "__main__":
    main()
