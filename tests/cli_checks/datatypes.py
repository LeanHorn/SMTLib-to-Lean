"""Datatype constructors, selectors, testers, match semantics, and native scopes."""

from .support import ROOT, run, check_generated, check_lean


def check_collisions(lean, tmp):
    output = tmp / "binding-collisions"
    run(ROOT / "tests/translation/bindings/collisions.smt2", "--out", output)
    generated = check_generated(lean, output, count=2)
    assert "c0_true" in generated and "c1_false" in generated
    # An arbitrary function may return negative values. Constructor names must
    # remain distinct from Boolean literals in both the model and refutation.
    checked = tmp / "BindingCollisions.lean"
    checked.write_text(generated.split("-- Proofs\n", 1)[0] + r'''
theorem first_has_model : ¬ Refutation_1 := by
  intro h
  apply h (fun i => -i - 1) SMT.Datatypes.g0.T0_flag.c1_false
  exact ⟨rfl, rfl, rfl, rfl, rfl, True.intro, fun h => h, rfl, True.intro⟩

theorem second_is_inconsistent : Refutation_2 := by
  intro _ _ h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, bad⟩
  cases bad
''')
    check_lean(lean, checked, complete=True)
    print("Binding collisions passed: original constructor names, Boolean literals, and two completed proofs")


def check_datatypes(lean, tmp):
    check_collisions(lean, tmp)
    fixtures = ROOT / "tests/translation/datatypes"
    for fixture, goal, count in [("constructors", "Refutation", 1),
                                 ("chc", "Problem", 1), ("sessions", "Refutation", 10),
                                 ("selectors", "Refutation", 1), ("selectors-chc", "Problem", 1),
                                 ("matches", "Refutation", 1), ("matches-chc", "Problem", 1)]:
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

    # Wrong-constructor results may differ, but equal inputs must agree.
    declarations = "(declare-datatype D ((has (field Int)) (other (tag Int)))) "
    source, output = tmp / "selector-laws.smt2", tmp / "selector-laws"
    source.write_text("(set-logic ALL) " + declarations + """
(assert (= (field (has 7)) 7))
(assert (distinct (field (other 1)) (field (other 2))))
(check-sat)
(assert (distinct (field (other (+ 0 1))) (field (other 1))))
(check-sat)
""")
    run(source, "--out", output)
    generated = check_generated(lean, output, count=2)
    checked = tmp / "SelectorLaws.lean"
    checked.write_text(generated.split("-- Proofs\n")[0] + r'''
theorem different_inputs : ¬ Refutation_1 := by
  intro h
  apply h (fun d => SMT.Datatypes.g0.T0_D.casesOn d (fun _ => 0) (fun i => i))
  exact ⟨rfl, by change (1 : Int) ≠ 2; decide⟩
theorem equal_inputs : Refutation_2 := by
  intro choice h
  exact h.2.2 rfl
example (choice : SMT.Datatypes.g0.T0_D → Int) (x : Int) :
    SMT.Selectors.g0.T0_D.s0_0_field choice (SMT.Datatypes.g0.T0_D.c0_has x) = x := rfl
''')
    check_lean(lean, checked, complete=True)

    # CHC choices are existential and precede the relations: exhibit a concrete model.
    source, output = tmp / "selector-model.smt2", tmp / "selector-model"
    source.write_text("(set-logic HORN) " + declarations + """
(declare-fun R (Int) Bool)
(assert (R (field (has 7))))
(assert (=> (= (field (other 1)) (field (other 2))) false))
(check-sat)
""")
    run(source, "--out", output)
    generated = check_generated(lean, output, goal="Problem")
    checked = tmp / "SelectorModel.lean"
    checked.write_text(generated.replace("  sorry\n", """
  refine ⟨(fun d => SMT.Datatypes.g0.T0_D.casesOn d (fun _ => 0) (fun i => i)),
    (fun _ => True), True.intro, ?_⟩
  change (1 : Int) ≠ 2
  decide
"""))
    check_lean(lean, checked, complete=True)

    # Complete the emitted obligation: binders, repeated branches, catch-all, and testers.
    source, output = tmp / "match-laws.smt2", tmp / "match-laws"
    source.write_text("""(set-logic ALL)
(declare-datatype D ((a) (b (value Int))))
(define-fun get ((d D) (x Int)) Int (match d ((a x) ((b x) x))))
(assert (not (and
  (forall ((x Int)) (= (get (b (+ x 1)) x) (+ x 1)))
  (forall ((x Int)) (= (get a x) x))
  (= (match (b 7) (((b x) x) ((b y) (+ y 1)) (rest 0))) 7)
  (= (match (b 7) ((whole whole) ((b x) a))) (b 7))
  (forall ((d D)) (= (match d (((b _) 7) (_ 3)))
                     (match d (((b ignored) 7) (rest 3)))))
  ((_ is b) (b 7)) (not (is-b a)))))
(check-sat)
""")
    run(source, "--out", output)
    generated = check_generated(lean, output)
    checked = tmp / "MatchLaws.lean"
    checked.write_text(generated.replace("  sorry\n", """
  intro h
  apply h
  exact ⟨fun _ => rfl, fun _ => rfl, rfl, rfl, fun _ => rfl, True.intro, fun h => h⟩
""") + r'''
example (d : SMT.Datatypes.g0.T0_D) :
    SMT.Testers.g0.T0_D.c1_b d ↔ ∃ x, d = SMT.Datatypes.g0.T0_D.c1_b x := by
  cases d with
  | c0_a =>
    constructor
    · intro h; exact False.elim h
    · rintro ⟨_, h⟩; cases h
  | c1_b x => exact ⟨fun _ => ⟨x, rfl⟩, fun _ => True.intro⟩
''')
    check_lean(lean, checked, complete=True)

    source, output = tmp / "match-model.smt2", tmp / "match-model"
    source.write_text("""(set-logic HORN)
(declare-datatype D ((a) (b (value Int))))
(declare-fun R (Int) Bool)
(assert (R (match (b 7) (((b x) x) (rest 0)))))
(assert (=> ((_ is a) (b 7)) false))
(check-sat)
""")
    run(source, "--out", output)
    generated = check_generated(lean, output, goal="Problem")
    checked = tmp / "MatchModel.lean"
    checked.write_text(generated.replace("  sorry\n",
                      "  exact ⟨fun _ => True, True.intro, fun h => h⟩\n"))
    check_lean(lean, checked, complete=True)

    # Reject malformed/unsupported terms without leaving a partial session artifact.
    common = "(set-logic ALL) (declare-datatype D ((a) (b (field Int)))) (check-sat) "
    rejected = [
        ("selector-sort", common + "(assert (= (field 0) 0))", ""),
        ("selector-arity", common + "(assert (= (field a a) 0))", ""),
        ("selector-scope", "(set-logic ALL) (push 1) "
         "(declare-datatype D ((a (field Int)))) (check-sat) (pop 1) "
         "(assert (= (field (a 0)) 0))", ""),
        ("selector-const", "(set-logic ALL) "
         "(declare-datatype D ((box (|const| (Array Int Int))))) "
         "(assert (= (select ((as |const| (Array Int Int)) 0) 0) 0))",
         "Type ascription"),
        ("tester-sort", common + "(assert ((_ is a) 0))", ""),
        ("tester-arity", common + "(assert ((_ is a) a a))", ""),
        ("match-incomplete", common + "(assert (match a ((a true))))", "exhaustive"),
        ("match-result", common + "(assert (match a ((a true) ((b x) 0))))", ""),
        ("match-nested", common + "(assert (match a ((a true) ((b (b x)) false))))", ""),
        ("match-scope", common + "(assert (and (match a ((a true) ((b x) true))) (= x 0)))", ""),
        ("match-dead-operator", common + "(assert (= (match a ((rest 0) ((b x) (^ x 2)))) 0))",
         "unsupported operator"),
        ("match-duplicate-variable", "(set-logic ALL) "
         "(declare-datatype D ((a) (b (left Int) (right Int)))) (check-sat) "
         "(assert (match a ((a true) ((b x x) true))))", "duplicate match pattern variable"),
        ("match-shadow-const", common +
         "(assert (= (match a ((a 0) ((b const) (select ((as const (Array Int Int)) 0) 0)))) 0))", ""),
        ("match-horn-relation", "(set-logic HORN) (declare-datatype D ((a) (b))) "
         "(declare-fun R (D) Bool) (check-sat) "
         "(assert (=> (match a ((a false) (rest (R rest)))) false)) (check-sat)", "CHC relation inside"),
        ("match-horn-quantifier", "(set-logic HORN) (declare-datatype D ((a) (b))) (check-sat) "
         "(assert (=> (match a ((a false) (rest (forall ((x Int)) (= x x))))) false)) (check-sat)",
         "leading forall"),
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
