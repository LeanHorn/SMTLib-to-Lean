"""Two compact sessions, checked meanings/proofs, and fail-closed dialect boundaries."""
from .support import ROOT, run, read_generated, check_lean


def check_profiles(lean, tmp):
    fixtures = ROOT / "tests/translation"
    model_input = fixtures / "chc/general-model.smt2"
    output = tmp / "general-model"
    run(model_input, "--out", output, "--mode", "model")
    generated = read_generated(output, goal="Model", count=3)
    assert "Outside the Flex Horn adapter" in generated
    check_lean(lean, output / "Query.lean", allow_sorry=True)
    proof = output / "Checked.lean"
    proof.write_text(generated.split("-- Proofs\n", 1)[0] + """
example : Model_1 ↔ ∃ (_c : Int) (p q : Int → Prop),
    (∃ x, p x) ∧ (∀ x, p x ∨ q x) ∧ (∀ x, ¬(p x ∧ q x)) := Iff.rfl

theorem model_sat : Model_1 :=
  ⟨0, fun _ => True, fun _ => False, ⟨0, True.intro⟩,
    fun _ => Or.inl True.intro, fun _ h => h.2⟩

theorem model_unsat : ¬Model_2 := by
  rintro ⟨c, p, q, ⟨x, hx⟩, _, _, absent⟩
  exact absent x hx

theorem after_pop : Model_3 := model_sat
""")
    check_lean(lean, proof, complete=True)
    rejected = tmp / "strict-horn"
    assert "CHC" in run(model_input, "--out", rejected, code=1).stderr
    assert not rejected.exists()

    output = tmp / "fixedpoint"
    fixture = fixtures / "fixedpoint/reachability.smt2"
    run(fixture, "--mode", "fixedpoint", "--out", output)
    generated = read_generated(output, goal="Safe", count=3)
    assert "Z3 query verdict: unsat" in generated and "Z3 query verdict: sat" in generated
    assert "unexecuted request" in generated
    assert ':10:1-10:12 (query 1: query, command 9)' in generated
    assert '(rule "seed")' in generated
    for i in range(1, 4):
        assert f"def Reachable_{i} : Prop := ¬Safe_{i}" in generated
    check_lean(lean, output / "Query.lean", allow_sorry=True)
    proof = output / "Checked.lean"
    proof.write_text(generated.split("-- Proofs\n", 1)[0].replace("import Init", "import Lean", 1) + """
example : Safe_1 ↔ ∃ (r : Int → Prop) (bad : Prop),
    (∀ _x : Int, r 0) ∧ (∀ x, r x → r (x + 1)) ∧
    (∀ x, r x → x < 0 → bad) ∧ (bad → False) := Iff.rfl

theorem first_safe : Safe_1 := by
  refine ⟨fun x => 0 ≤ x, False, ?_, ?_, ?_, ?_⟩
  · intro; omega
  · intro x hx; omega
  · intro x hx hn; omega
  · exact id

theorem second_reachable : Reachable_2 := by
  rintro ⟨r, bad, seed, _, _, excluded⟩
  exact excluded 0 (seed 0)

theorem third_reachable : Reachable_3 := by
  rintro ⟨r, bad, _, _, _, fact, excluded⟩
  exact excluded (fact 0)
""")
    check_lean(lean, proof, complete=True)

    source, output = tmp / "typed-rules.smt2", tmp / "typed-rules"
    source.write_text("""
(declare-rel |mixed; relation| (Bool (_ BitVec 2) Real))
(declare-var x Int)
(declare-var |smt2lean.query.0| (_ BitVec 2))
(rule (forall ((x Real))
  (=> (= x 1.0) (|mixed; relation| true |smt2lean.query.0| x))))
(query |mixed; relation|)
""")
    run(source, "--out", output, "--mode", "fixedpoint")
    generated = read_generated(output, goal="Safe")
    proof = output / "Checked.lean"
    proof.write_text(generated.split("-- Proofs\n", 1)[0] + """
theorem typed_reachable : Reachable := by
  rintro ⟨r, seed, excluded⟩
  exact excluded True 0 1 (seed 0 0 1 rfl)
""")
    check_lean(lean, proof, complete=True)

    # Early and late failures must leave no partial output. Small generated cases
    # avoid storing one fixture per rejection or paying for additional Lean runs.
    prefix = "(declare-rel P (Int))(declare-var x Int)(rule (P 0))(query P)"
    for i, (tail, reason) in enumerate([
        ("(push 1)", "unsupported fixedpoint command"),
        ("(query (P 0))", "expected one symbol"),
        ("(query Missing)", "declared relation"),
        ("(query P :print-answer true)", "without query options"),
        ("(declare-var |x| Int)", "duplicate fixedpoint symbol"),
        ("(declare-rel A ((Array Int Int)))", "supports Bool, Int, Real"),
        ("(rule (=> (not (P x)) (P (+ x 1))))(query P)", "theory guard"),
        ("(rule false)(query P)", "positive relation head"),
        ("(rule (exists ((y Int)) (P y)))(query P)", "quantifier"),
        ("(rule (=> (= (div x 0) 1) (P x)))(query P)", "nonzero literal divisor"),
        ("(exit)(rule (P 1))", "after exit"),
    ]):
        source, target = tmp / f"bad-profile-{i}.smt2", tmp / f"bad-profile-{i}"
        source.write_text(prefix + tail)
        result = run(source, "--out", target, "--mode", "fixedpoint", code=1)
        assert reason in result.stderr, result.stderr
        assert not target.exists()
    for mode in ["unknown", "", "HORN"]:
        run(model_input, "--out", tmp / "bad-mode", "--mode", mode, code=2)
    print("Profiles passed: general models, strict Horn isolation, fixedpoint snapshots/polarity, completed proofs and rejections")
