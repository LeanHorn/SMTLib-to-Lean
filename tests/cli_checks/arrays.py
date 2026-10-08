from .support import (ROOT, read_generated, CHC, run, check_lean, check_generated)

def check_array_sharing(lean, tmp):
    """Repeated stores must stay compact and usable in an admission-free proof."""
    sizes = []
    for depth in [5, 15]:
        term = f"(not (= (select a{depth} 0) (select a{depth} 0)))"
        for i in range(depth, 0, -1):
            term = f"(let ((a{i} (store a{i-1} {i} (select a{i-1} 0)))) {term})"
        source, output = tmp / f"sharing-{depth}.smt2", tmp / f"sharing-{depth}"
        source.write_text("(set-logic QF_AUFLIA)(declare-const a0 (Array Int Int))"
                          f"(assert {term})(check-sat)")
        run(source, "--out", output)
        generated = read_generated(output)
        assert "let " in generated, generated
        sizes.append(len(generated.encode()))
        query = output / "Query.lean"
        query.write_text(generated.split("-- Proofs\n", 1)[0] +
                         "theorem checked : Refutation := by\n"
                         "  intro A read write a laws impossible\n"
                         "  exact impossible rfl\n")
        check_lean(lean, query, complete=True)
    assert sizes[1] < 25000 and sizes[1] < 4 * sizes[0], sizes
    print("Array sharing passed: compact nested stores and two completed proofs")

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
        generated = read_generated(output)
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
        generated = (read_generated(output, goal=goal) if name == "horn-constants"
                     else check_generated(lean, output, goal=goal))
        generated_fixtures[name] = generated

    cases = [
        ("constant-read", "(declare-const i Int)"
         "(assert (distinct (select ((as const (Array Int Int)) 0) i) 0))",
         "  intro A read write const i laws bad\n  exact bad (laws.2 0 i)\n"),
        ("symbolic-read", "(declare-const v Int)(declare-const i Int)"
         "(assert (distinct (select ((as const (Array Int Int)) v) i) v))",
         "  intro A read write const v i laws bad\n  exact bad (laws.2 v i)\n"),
        ("constant-store-same", "(declare-const v Int)(declare-const i Int)"
         "(assert (distinct (select (store ((as const (Array Int Int)) v) i 7) i) 7))",
         "  intro A read write const v i laws bad\n  exact bad (laws.1.2.1 (const v) i 7)\n"),
        ("constant-store-other", "(declare-const v Int)(declare-const i Int)(declare-const j Int)"
         "(assert (distinct i j))"
         "(assert (distinct (select (store ((as const (Array Int Int)) v) i 7) j) v))",
         "  intro A read write const v i j laws h\n"
         "  exact h.2 ((laws.1.2.2.1 (const v) i j 7 h.1).trans (laws.2 v j))\n"),
        ("unequal-constants", "(declare-sort I 0)(declare-const v Int)(declare-const w Int)"
         "(assert (distinct v w))"
         "(assert (= ((as const (Array I Int)) v) ((as const (Array I Int)) w)))",
         "  intro I inhabited A read write const v w laws h\n"
         "  obtain ⟨i⟩ := inhabited\n"
         "  have same := congrArg (fun a => read a i) h.2\n"
         "  rw [laws.2 v i, laws.2 w i] at same\n  exact h.1 same\n"),
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
        generated = read_generated(output)
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
    (fun a => a 0 = 0), laws, ?_, rfl, ?_, ?_, ?_⟩
  · intro v i; rfl
  · intro a _; simp [write]
  · intro a same different; exact different same
  · intro v h; exact h

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
(reset)
(set-option :global-declarations true)
(set-logic ALL)
(push 1)
(assert (and (! true :named unrelated) (= (select ((as const (Array Int Int)) 0) 0) 0)))
(pop 1)
(check-sat-assuming (unrelated))
(push 1)
(assert (! (let ((erased ((as const (Array Int Int)) 1))) true) :named kept))
(pop 1)
(check-sat-assuming (kept))
(reset-assertions)
(check-sat-assuming (kept))
(reset)
(push 1)
(assert (= (select ((as const (Array Int Int)) 2) 0) 2))
(pop 1)
(assert (= (select ((as const (Array Int Int)) 3) 0) 3))
(check-sat)
(reset-assertions)
(check-sat)
""")
    run(source, "--out", output)
    generated = check_generated(lean, output, count=12)
    for number in range(1, 13):
        body = generated.split(f"def Refutation_{number} : Prop :=\n", 1)[1]
        body = body.split("-- Source:", 1)[0].split("-- Proofs", 1)[0]
        assert ("SMT.constArrayLaw" in body) == (number in [2, 4, 6, 9, 10, 11]), (number, body)
    for name, tail in [
        ("erased-wrong-payload", "(assert (let ((ignored ((as const (Array Int Int)) true))) true))"),
        ("unbound-payload", "(assert (= (select ((as const (Array Int Int)) missing) 0) 0))"),
        ("wrong-index", "(assert (= (select ((as const (Array Int Int)) 0) true) 0))"),
        ("string-sort", "(declare-const unsupported (Array Int (Array Int String)))"),
    ]:
        source, output = tmp / f"arrays-extended-bad-{name}.smt2", tmp / f"arrays-extended-bad-{name}"
        source.write_text("(set-logic ALL)(assert (= (select ((as const (Array Int Int)) 0) 0) 0))"
                          "(check-sat)" + tail)
        result = run(source, "--out", output, code=1)
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
    run(source, "--out", output)
    generated = check_generated(lean, output, count=2)
    assert "SMT.constArrayLaw" in generated.split("def Refutation_2 : Prop :=", 1)[1]
    assert "smt2lean.internal." not in generated
    source, output = tmp / "arrays-hidden-relation.smt2", tmp / "arrays-hidden-relation"
    source.write_text("(set-logic HORN)(declare-fun P (Int) Bool)"
                      "(declare-fun R ((Array Int Bool)) Bool)"
                      "(assert (forall ((x Int)) (R ((as const (Array Int Bool)) (P x)))))"
                      "(check-sat)")
    assert "CHC relation inside" in run(source, "--out", output, code=1).stderr
    assert not output.exists()
    print("Extended array CLI passed: symbolic constants, completed proofs, scope snapshots, and rejected payloads")

