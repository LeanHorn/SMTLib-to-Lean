from .support import (ROOT, read_generated, INTEGERS, CHC, run, check_lean, check_generated, unfold_statement)


def check_integer_division(lean, tmp):
    """Check model choices at zero and translate the complete original CHC corpus."""
    for fixture, goal in [(INTEGERS / "division.smt2", "Refutation"), (CHC / "division.smt2", "Problem")]:
        output = tmp / f"division-{goal}"
        run(fixture, "--out", output)
        check_generated(lean, output, goal=goal)
    # Keep standalone compilation of the original corpus; clause counts live in testHorn.
    for name in ["lh_sum_rec", "lh_abs_neg", "flux_sum_off_by_one", "flux_bsearch"]:
        output = tmp / f"corpus-{name}"
        run(ROOT / f"tests/chc/{name}.smt2", "--out", output)
        generated = check_generated(lean, output, goal="Problem")
        assert "divZero" not in generated and "modZero" not in generated, name
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
        generated = read_generated(output, goal="Problem" if logic == "HORN" else "Refutation")
        completed = output / "Query.lean"
        completed.write_text(generated.split("-- Proofs\n", 1)[0] + f"theorem checked : {target} := by\n"
                             + unfold_statement(generated, target) + proof)
        check_lean(lean, completed, complete=True)
    print("Integer division passed: six completed semantic proofs; all four original CHCs elaborate")


def check_reals(lean, tmp):
    """Exact Real arithmetic and model choices, compiled using the pinned Mathlib profile."""
    for fixture, goal in [(ROOT / "tests/translation/real/arithmetic.smt2", "Refutation"),
                          (CHC / "real.smt2", "Problem")]:
        output = tmp / f"real-{goal}"
        run(fixture, "--out", output)
        generated = check_generated(lean, output, goal=goal, template=(goal == "Refutation"))
        assert generated.startswith("import Mathlib.Data.Real.Basic\n")
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
        generated = read_generated(output, goal="Problem" if logic == "HORN" else "Refutation")
        if name in ("exact", "horn-linear"):
            assert "realDivZero" not in generated
        completed = output / "Query.lean"
        completed.write_text("import Mathlib.Tactic.NormNum\n" + generated.split("-- Proofs\n", 1)[0]
                             + f"theorem checked : {target} := by\n" + unfold_statement(generated, target) + proof)
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
        generated = read_generated(output, goal="Problem" if logic == "HORN" else "Refutation")
        if name == "implicit-cast":
            assert generated.startswith("import Mathlib.Data.Real.Basic\n")
        completed = output / "Query.lean"
        completed.write_text("import Mathlib.Tactic.NormNum\n" + generated.split("-- Proofs\n", 1)[0]
                             + f"theorem checked : {target} := by\n" + unfold_statement(generated, target) + proof)
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
