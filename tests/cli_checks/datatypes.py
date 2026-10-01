"""Datatype translation, constructor semantics, and native scope regressions."""

from .support import ROOT, run, check_generated, check_lean


def check_datatypes(lean, tmp):
    fixtures = ROOT / "tests/translation/datatypes"
    for fixture, goal, count in [("constructors", "Refutation", 1),
                                 ("chc", "Problem", 1), ("sessions", "Refutation", 9)]:
        output = tmp / f"datatypes-{fixture}"
        run(fixtures / f"{fixture}.smt2", "--out", output)
        generated = check_generated(lean, output, goal=goal, count=count)
        assert "inductive SMT.Datatypes." in generated
        assert "import Smt" not in generated and "axiom " not in generated
        if fixture == "constructors":
            assert "mutual\n" in generated and "Field0 : Type" in generated
            assert "field0 : Prop" in generated and "SMT.arrayLaws" in generated
        edited = generated + "\n-- Preserve user proof work.\n"
        (output / "Query.lean").write_text(edited)
        run(fixtures / f"{fixture}.smt2", "--out", output, code=1)
        assert (output / "Query.lean").read_text() == edited

    # Complete actual emitted obligations and check the free-constructor laws.
    text = """(set-logic ALL)
(declare-datatype Color ((red) (blue)))
(declare-datatype Counter ((zero) (step (previous Counter))))
(declare-datatype Pair ((pair (left Int) (right Int))))
(assert (= red blue))
(check-sat)
"""
    text = text.replace("(assert (= red blue))", """(declare-const n Counter)
(declare-const p Pair)
(assert (= n n))
(assert (= p p))
(assert (= red blue))""")
    source, output = tmp / "datatype-laws.smt2", tmp / "datatype-laws"
    source.write_text(text)
    run(source, "--out", output)
    generated = check_generated(lean, output)
    proofs = generated.replace("  sorry\n", "  intro _ _ h\n  cases h.2.2\n") + r'''
open SMT.Datatypes.g0
example (x y : Int) : T0_Pair.c0_pair x y = T0_Pair.c0_pair 3 4 → x = 3 ∧ y = 4 := by
  intro h
  cases h
  exact ⟨rfl, rfl⟩
example (c : T0_Color) : c = T0_Color.c0_red ∨ c = T0_Color.c1_blue := by
  cases c with
  | c0_red => exact Or.inl rfl
  | c1_blue => exact Or.inr rfl
example (n : T0_Counter) : n ≠ T0_Counter.c1_step n := by
  induction n with
  | c0_zero => intro h; cases h
  | c1_step n ih =>
    intro h
    exact ih (T0_Counter.c1_step.inj h)
'''
    checked = tmp / "DatatypeLaws.lean"
    checked.write_text(proofs)
    check_lean(lean, checked, complete=True)

    # A true CHC model and an inconsistent CHC model keep the same positive goal kind.
    for assertion, suffix, proof in [
        ("(assert (R red))", "model", "  exact ⟨fun _ => True, True.intro⟩\n"),
        ("(assert (R red)) (assert (=> (R red) false))", "inconsistent", None),
    ]:
        source = tmp / f"datatype-chc-{suffix}.smt2"
        source.write_text("(set-logic HORN) (declare-datatype Color ((red) (blue))) "
                          "(declare-fun R (Color) Bool) " + assertion + " (check-sat)")
        output = tmp / f"datatype-chc-{suffix}"
        run(source, "--out", output)
        generated = check_generated(lean, output, goal="Problem")
        checked = tmp / f"DatatypeChc{suffix}.lean"
        if proof:
            checked.write_text(generated.replace("  sorry\n", proof))
        else:
            checked.write_text(generated.split("-- Proofs\n")[0] +
                               "theorem inconsistent : ¬ Problem := by\n"
                               "  rintro ⟨R, h, bad⟩\n  exact bad h\n")
        check_lean(lean, checked, complete=True)

    # Real can appear only in a datatype's fields; emission must still import Mathlib.
    source = tmp / "datatype-real.smt2"
    source.write_text("(set-logic ALL) (declare-datatype Box ((box (value Real)))) "
                      "(declare-const b Box) (assert (= b b)) (check-sat)")
    output = tmp / "datatype-real"
    run(source, "--out", output)
    assert check_generated(lean, output).startswith("import Mathlib.Data.Real.Basic")

    # Reject later unsupported features without leaving a partial session artifact.
    common = "(set-logic ALL) (declare-datatype D ((a) (b (field Int)))) (check-sat) "
    rejected = [
        ("selector", common + "(assert (= (field a) 0))", "APPLY_SELECTOR"),
        ("tester", common + "(assert ((_ is a) a))", "APPLY_TESTER"),
        ("match", common + "(assert (match a ((a true) ((b x) false))))", "MATCH"),
        ("parametric", "(set-logic ALL) (declare-datatypes ((List 1)) "
         "((par (T) ((nil) (cons (head T) (tail (List T)))))))", "parametric"),
        ("nested", "(set-logic ALL) (declare-datatype D ((a) (b (field (Array Int D)))))",
         "nested datatype recursion"),
        ("field-sort", "(set-logic ALL) (declare-datatype D ((a (field String))))",
         "unsupported datatype field sort"),
        ("no-base", "(set-logic ALL) (declare-datatype D ((step (previous D))))",
         "well-founded"),
    ]
    for name, text, reason in rejected:
        source, output = tmp / f"datatype-bad-{name}.smt2", tmp / f"datatype-bad-{name}"
        source.write_text(text)
        result = run(source, "--out", output, code=1)
        assert reason in result.stderr, result.stderr
        assert "command " in result.stderr and not output.exists()
