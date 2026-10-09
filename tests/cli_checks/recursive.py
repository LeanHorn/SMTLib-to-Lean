"""Recursive equations and ground sort instances: compact sessions with checked proofs."""
from .support import ROOT, run, read_generated, check_lean


def checked(lean, output, source, proofs):
    file = output / "Checked.lean"
    file.write_text(source.split("-- Proofs\n", 1)[0].replace("import Init", "import Lean", 1) + proofs)
    check_lean(lean, file, complete=True)


def check_recursive(lean, tmp):
    fixtures = ROOT / "tests/translation/recursive"
    output = tmp / "functions"
    run(fixtures / "functions.smt2", "--out", output)
    source = read_generated(output)
    assert "let a :=" in source and "Definitions.inc" in source
    check_lean(lean, output / "Query.lean", allow_sorry=True)
    checked(lean, output, source, """
example : Refutation_1.Assertion002 =
    (fun f g : Int → Int => ∀ n, f n = if n ≤ 0 then n else g (n - 1) + 1) := rfl
example : Refutation_1.Assertion003 =
    (fun f g : Int → Int => ∀ n, g n = if n ≤ 0 then n else f (n - 1) + 1) := rfl

theorem fib_four : Refutation := by
  intro fib left right h
  rcases h with ⟨hf, _, _, bad⟩
  have h0 := hf 0
  have h1 := hf 1
  have h2 := hf 2
  have h3 := hf 3
  have h4 := hf 4
  simp at h0 h1 h2 h3 h4
  apply bad
  omega
""")
    for mode, goal in [("auto", "Refutation"), ("model", "Model")]:
        output = tmp / f"scopes-{mode}"
        run(fixtures / "scopes.smt2", "--mode", mode, "--out", output)
        source = read_generated(output, goal=goal, count=7)
        if mode == "auto":
            proofs = """
example : Refutation_2 ↔ (∀ n : Int, n = n + 1 → False) := Iff.rfl
example : Refutation_5 ↔ (∀ f g : Int, f = g + 1 ∧ g = f → False) := Iff.rfl
example : Refutation_6 ↔ Refutation_5 := Iff.rfl
example : Refutation_2 := by intro n h; change n = n + 1 at h; omega
example : Refutation_5 := by
  intro f g h
  change f = g + 1 ∧ g = f at h
  omega
"""
            proofs += "\n".join(f"example : ¬Refutation_{i} := fun h => h True.intro" for i in [1, 3, 4, 7])
        else:
            proofs = """
example : Model_2 ↔ (∃ n : Int, n = n + 1) := Iff.rfl
example : Model_5 ↔ (∃ f g : Int, f = g + 1 ∧ g = f) := Iff.rfl
example : Model_6 ↔ Model_5 := Iff.rfl
example : ¬Model_2 := by rintro ⟨n, h⟩; change n = n + 1 at h; omega
example : ¬Model_5 := by
  rintro ⟨f, g, h⟩
  change f = g + 1 ∧ g = f at h
  omega
"""
            proofs += "\n".join(f"example : Model_{i} := True.intro" for i in [1, 3, 4, 7])
        checked(lean, output, source, proofs)
    output = tmp / "sorts"
    run(fixtures / "sorts.smt2", "--out", output)
    source = read_generated(output, count=5)
    checked(lean, output, source, """
example : Refutation_1 ↔
    (∀ (A B C D : Type), Nonempty A → Nonempty B → Nonempty C → Nonempty D →
      ∀ (x y : A) (_b : B) (_wrap : A → C) (ident : A → A),
        (∀ v, ident v = v) ∧ x = y ∧ ¬ident x = y ∧ (∀ r : D, r = r) → False) := Iff.rfl
example : Refutation_3 ↔ Refutation_1 := Iff.rfl
example : Refutation_1 := by
  intro A B C D _ _ _ _ x y b wrap ident h
  exact h.2.2.1 ((h.1 x).trans h.2.1)
example : ¬Refutation_4 := fun h => h Unit ⟨()⟩ (fun _ => rfl)
example : ¬Refutation_5 := fun h => h True.intro
""")
    # Constructor aliases also work in QF logics and private constant-array indices.
    source, output = tmp / "recursive-arrays.smt2", tmp / "recursive-arrays"
    source.write_text("""(set-logic QF_AUFLIA)
(declare-sort Box 1)(declare-const x (Box (Box Int)))(declare-const n Int)
(assert (distinct (select ((as const (Array (Box (Box Int)) Int)) n) x) n))
(check-sat)(push 1)
(declare-sort Pair 2)(declare-const y (Pair Int Bool))
(assert (= (select ((as const (Array (Pair Int Bool) Int)) n) y) n))
(check-sat)(pop 1)(check-sat)
(reset)(set-logic ALL)
(declare-datatype List ((nil) (cons (head Int) (tail List))))
(define-fun-rec size ((xs List)) Int (match xs ((nil 0) ((cons h t) (+ 1 (size t))))))
(define-fun-rec fill ((n Int)) (Array Int Int)
  (ite (<= n 0) ((as const (Array Int Int)) n) (fill (- n 1))))
(assert (distinct (select (fill 0) (size nil)) 0))(check-sat)
""")
    run(source, "--out", output)
    checked(lean, output, read_generated(output, count=4), """
example : Refutation_3 ↔ Refutation_1 := Iff.rfl
example : Refutation_1 := by
  intro A B _ _ Array select store const x n laws bad
  exact bad (laws.2 n x)
""")
    # Both functions are registered before either body, including native-name collisions.
    source, output = tmp / "recursive-bool.smt2", tmp / "recursive-bool"
    source.write_text("""(set-logic HORN)
(define-funs-rec ((set.card ((n Int)) Bool) (other ((n Int)) Bool))
  ((other n) (set.card n)))
(assert (set.card 0))(check-sat)
""")
    run(source, "--mode", "model", "--out", output)
    generated = read_generated(output, goal="Model")
    checked(lean, output, generated, """
example : Model ↔ (∃ f g : Int → Prop, (∀ n, f n = g n) ∧ (∀ n, g n = f n) ∧ f 0) := Iff.rfl
example : Model := ⟨fun _ => True, fun _ => True, fun _ => rfl, fun _ => rfl, True.intro⟩
""")
    rejected = tmp / "recursive-bool-horn"
    run(source, "--out", rejected, code=1)
    assert not rejected.exists()
    for i, body in enumerate([
        "(define-fun-rec f ((x Int)) Int (^ x 2))",
        "(define-funs-rec ((f () Int) (g () Int)) (g))",
        "(define-fun-rec f ((x String)) Int 0)",
        "(declare-sort S 1)(declare-const x (S Int Bool))",
        "(push 1)(define-fun-rec f () Int f)(pop 1)(assert (= f 0))",
        "(push 1)(declare-sort S 1)(pop 1)(declare-const x (S Int))",
    ]):
        source, output = tmp / f"rec-bad-{i}.smt2", tmp / f"rec-bad-{i}"
        source.write_text("(set-logic ALL)(check-sat)" + body + "(check-sat)")
        run(source, "--out", output, code=1)
        assert not output.exists()
    print("Recursive definitions passed: Fibonacci proof, mutual equations, unused inconsistency, scopes, sort carriers and rejections")
