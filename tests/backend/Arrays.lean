import tests.backend.Support
import tests.backend.ArrayModel

open Lean Meta Qq Classical
open Smt2Lean.Tests
open Smt2Lean.Backend Smt2Lean.Translate Smt2Lean.Emit

-- Expand the contract here so expected propositions do not depend on emitted helpers.
set_option quotPrecheck false in
local notation "arrayLaws" => (fun (I E A : Type) (read : A → I → E)
  (write : A → I → E → A) => Nonempty A ∧
    (∀ a i v, read (write a i v) i = v) ∧
    (∀ a i j v, i ≠ j → read (write a i v) j = read a j) ∧
    (∀ a b, (∀ i, read a i = read b i) → a = b))

private def checkStatement (query : ParsedQuery) (value expected : Expr)
    (kind : GoalKind := .refutation) (usesReal : Bool := false) : MetaM Unit := do
  let statement := match kind with
    | .refutation => `Refutation
    | .problem => `Problem
  checkEqual value expected
  if value.hasFVar || value.hasLooseBVars || value.hasMVar then
    throwError "array statement contains unresolved variables"
  checkEqual (← inferType value) q(Prop)
  checkStatementAxioms statement
  let source ← render value kind query.source query.assertionSources
  unless source.startsWith (if usesReal then "import Mathlib.Data.Real.Basic\n" else "import Init\n") do
    throwError "array output has the wrong imports"
  checkEmission value kind query.source query.assertionSources

private def checkArrayRefutation (query : ParsedQuery) (expected : Expr)
    (usesReal : Bool := false) : MetaM Unit := do
  checkStatement query (← defineRefutation query) expected (usesReal := usesReal)

private def checkBasic (env : Environment) : IO Unit :=
  runQuery env "flat array operations" "
    (set-logic ALL)
    (declare-const a (Array Int Int))
    (declare-const b (Array Int Int))
    (declare-const i Int)
    (declare-const j Int)
    (declare-const v Int)
    (declare-const p Bool)
    (declare-fun f ((Array Int Int) Int) (Array Int Int))
    (define-fun update ((x (Array Int Int)) (k Int)) (Array Int Int) (store x k v))
    (assert (= (select (store a i v) i) v))
    (assert (=> (distinct i j) (= (select (store a i v) j) (select a j))))
    (assert (= (store a i v) b))
    (assert (distinct a b (store a j v)))
    (assert (= (ite p a b) (f (update a i) j)))
    (assert (= (select (let ((x (store b j v))) x) i) (select b i)))
    (check-sat)" fun query => do
      checkArrayRefutation query q(∀ (A : Type) (read : A → Int → Int)
        (write : A → Int → Int → A) (a b : A) (i j v : Int) (p : Prop)
        (f : A → Int → A),
        arrayLaws Int Int A read write →
        (read (write a i v) i = v ∧
          (i ≠ j → read (write a i v) j = read a j) ∧
          write a i v = b ∧
          (a ≠ b ∧ a ≠ write a j v ∧ b ≠ write a j v) ∧
          (if p then a else b) = f (write a i v) j ∧
          read (write b j v) i = read b i) → False)

private def checkUnused (env : Environment) : IO Unit := do
  runQuery env "unused array function signature" "
    (set-logic ALL)
    (declare-fun unused ((Array Int Bool)) (Array Bool Int))
    (assert true)
    (check-sat)" fun query =>
      checkArrayRefutation query q(∀ (A : Type) (readA : A → Int → Prop)
        (writeA : A → Int → Prop → A)
        (B : Type) (readB : B → Prop → Int) (writeB : B → Prop → Int → B)
        (_unused : A → B),
        (arrayLaws Int Prop A readA writeA ∧ arrayLaws Prop Int B readB writeB) →
        True → False)
  runQuery env "unused array definition parameter" "
    (set-logic ALL)
    (define-fun unused ((a (Array Int Int))) Bool true)
    (assert true)
    (check-sat)" fun query =>
      checkArrayRefutation query q(∀ (A : Type) (read : A → Int → Int)
        (write : A → Int → Int → A), arrayLaws Int Int A read write → True → False)

private def checkSorts (env : Environment) : IO Unit :=
  runQuery env "mixed flat array sorts" "
    (set-logic ALL)
    (declare-sort U 0)
    (declare-const a (Array Bool Int))
    (declare-const b (Array Int Bool))
    (declare-const c (Array Real (_ BitVec 4)))
    (declare-const d (Array U U))
    (declare-const u U)
    (declare-const p Bool)
    (declare-const i Int)
    (declare-const r Real)
    (declare-const v (_ BitVec 4))
    (assert (= (select (store a p i) p) i))
    (assert (= (select (store b i p) i) p))
    (assert (= (select (store c r v) r) v))
    (assert (= (select (store d u u) u) u))
    (check-sat)" fun query =>
      checkArrayRefutation query (usesReal := true) q(∀ U : Type, Nonempty U →
        ∀ (A : Type) (readA : A → Prop → Int) (writeA : A → Prop → Int → A)
          (B : Type) (readB : B → Int → Prop) (writeB : B → Int → Prop → B)
          (C : Type) (readC : C → Real → BitVec 4) (writeC : C → Real → BitVec 4 → C)
          (D : Type) (readD : D → U → U) (writeD : D → U → U → D)
          (a : A) (b : B) (c : C) (d : D) (u : U) (p : Prop) (i : Int)
          (r : Real) (v : BitVec 4),
        (arrayLaws Prop Int A readA writeA ∧ arrayLaws Int Prop B readB writeB ∧
          arrayLaws Real (BitVec 4) C readC writeC ∧ arrayLaws U U D readD writeD) →
        (readA (writeA a p i) p = i ∧ readB (writeB b i p) i = p ∧
          readC (writeC c r v) r = v ∧ readD (writeD d u u) u = u) → False)

private def checkIsolation (env : Environment) : IO Unit :=
  runQuery env "array reconstruction isolation" "
    (set-logic ALL)
    (declare-const a (Array Int Int))
    (assert (= (select a 0) 1))
    (check-sat)" fun query =>
      withAssertions query fun previous _ =>
        withAssertions query fun current assertions => do
          unless previous.size == 4 && current.size == 4 do
            throwError "expected one shared array model and one declaration"
          for old in previous do
            if current.contains old || assertions.any (·.containsFVar old.fvarId!) then
              throwError "separate array reconstructions share model parameters"

private def checkQuantified (env : Environment) : IO Unit := do
  runQuery env "quantified nested array models" "
    (set-logic ALL)
    (declare-const a (Array Int Int))
    (declare-const nested (Array (Array Int Int) (Array Int Int)))
    (assert (forall ((x (Array Int Int)))
      (exists ((y (Array Int Int))) (= (store x 0 1) y))))
    (assert (= (select (store nested a a) a) a))
    (assert (forall ((x (Array (Array Int Int) (Array Int Int)))) (= (select x a) a)))
    (assert (forall ((a (Array Int Int)))
      (let ((before a))
        (exists ((a (Array Int Int)))
          (and (= a (store before 0 1)) (= (select a 0) (select before 0)))))))
    (check-sat)" fun query =>
      checkArrayRefutation query q(∀ (A : Type) (readA : A → Int → Int)
        (writeA : A → Int → Int → A)
        (N : Type) (readN : N → A → A) (writeN : N → A → A → N)
        (a : A) (nested : N),
        (arrayLaws Int Int A readA writeA ∧ arrayLaws A A N readN writeN) →
        ((∀ x : A, ∃ y : A, writeA x 0 1 = y) ∧
          readN (writeN nested a a) a = a ∧ (∀ x : N, readN x a = a) ∧
          (∀ before : A, ∃ after : A,
            after = writeA before 0 1 ∧ readA after 0 = readA before 0)) → False)
  runQuery env "restricted arrays admit no identity" "
    (set-logic ALL)
    (assert (forall ((a (Array Int Int)))
      (exists ((i Int)) (distinct (select a i) i))))
    (check-sat)" fun query => do
      let expected : Q(Prop) := q(∀ (A : Type) (read : A → Int → Int)
        (write : A → Int → Int → A), arrayLaws Int Int A read write →
        (∀ a : A, ∃ i : Int, read a i ≠ i) → False)
      checkArrayRefutation query expected
      -- This translated refutation is false: a proper array model satisfies the input.
      let countermodel := q(fun h : ∀ (A : Type) (read : A → Int → Int)
          (write : A → Int → Int → A), arrayLaws Int Int A read write →
          (∀ a : A, ∃ i : Int, read a i ≠ i) → False =>
        h ArrayModel.Carrier ArrayModel.select ArrayModel.store
          ArrayModel.model_laws ArrayModel.restricted_model_misses_identity)
      checkEqual (← inferType countermodel) q(¬$expected)
      checkStatementAxioms ``ArrayModel.proper_model_with_constants
      checkStatementAxioms ``ArrayModel.full_functions_have_identity

private def checkConstants (env : Environment) : IO Unit := do
  runQuery env "nested constant array models" "
    (set-logic ALL)
    (define-fun zero () (Array Int Int) ((as const (Array Int Int)) 0))
    (declare-const i Int)
    (assert (= (select zero i) 0))
    (assert (= (select (store zero i 7) i) 7))
    (assert (= (select (select ((as const (Array Bool (Array Int Int)))
      ((as const (Array Int Int)) 2)) true) i) 2))
    (assert (forall ((a (Array Int Int))) (= (select (store a i (select zero i)) i) 0)))
    (check-sat)" fun query =>
      checkArrayRefutation query q(∀ (A : Type) (readA : A → Int → Int)
        (writeA : A → Int → Int → A) (constA : Int → A)
        (B : Type) (readB : B → Prop → A) (writeB : B → Prop → A → B)
        (constB : A → B) (i : Int),
        (arrayLaws Int Int A readA writeA ∧ (∀ v i, readA (constA v) i = v) ∧
          arrayLaws Prop A B readB writeB ∧ (∀ v p, readB (constB v) p = v)) →
        (readA (constA 0) i = 0 ∧ readA (writeA (constA 0) i 7) i = 7 ∧
          readA (readB (constB (constA 2)) True) i = 2 ∧
          (∀ a : A, readA (writeA a i (readA (constA 0) i)) i = 0)) → False)
  runQuery env "quoted annotation keyword is an ordinary function" "
    (set-logic ALL)
    (declare-fun |!| ((Array Int Int) Int) Bool)
    (declare-const x Int)
    (assert (|!| ((as const (Array Int Int)) x) 1))
    (check-sat)" fun query =>
      checkArrayRefutation query q(∀ (A : Type) (read : A → Int → Int)
        (write : A → Int → Int → A) (const : Int → A)
        (f : A → Int → Prop) (x : Int),
        (arrayLaws Int Int A read write ∧ (∀ v i, read (const v) i = v)) →
        f (const x) 1 → False)
  runQuery env "user function named const is not the array constructor" "
    (set-logic ALL)
    (declare-fun const (Int) (Array Int Int))
    (declare-const x Int)
    (assert (= ((as const (Array Int Int)) x) (const x)))
    (check-sat)" fun query =>
      checkArrayRefutation query q(∀ (A : Type) (read : A → Int → Int)
        (write : A → Int → Int → A) (f : Int → A) (x : Int),
        arrayLaws Int Int A read write → f x = f x → False)
  runQuery env "symbolic constant arrays with native binding scopes" "
    (set-logic ALL)
    (declare-const x Int)
    (define-fun fill ((x Int)) (Array Int Int) ((as const (Array Int Int)) x))
    (assert (forall ((x Int)) (= (select (fill (+ x 1)) x) (+ x 1))))
    (assert (let ((x 7)) (= (select ((as const (Array Int Int)) x) 0) x)))
    (assert (= (select ((as const (Array Int Int)) (! x :named payload)) 0) x))
    (assert (= (select ((as const (Array Int (Array Int Int))) (fill x)) 0) (fill x)))
    (check-sat)" fun query =>
      checkArrayRefutation query q(∀ (A : Type) (readA : A → Int → Int)
        (writeA : A → Int → Int → A) (constA : Int → A)
        (N : Type) (readN : N → Int → A) (writeN : N → Int → A → N)
        (constN : A → N) (x : Int),
        (arrayLaws Int Int A readA writeA ∧ (∀ v i, readA (constA v) i = v) ∧
          arrayLaws Int A N readN writeN ∧ (∀ v i, readN (constN v) i = v)) →
        ((∀ y : Int, readA (constA (y + 1)) y = y + 1) ∧
          readA (constA 7) 0 = 7 ∧ readA (constA x) 0 = x ∧
          readN (constN (constA x)) 0 = constA x) → False)
  for input in #[
      "(define-fun unused () (Array Int Int) ((as const (Array Int Int)) 3)) (assert true)",
      "(assert (let ((unused ((as const (Array Int Int)) 3))) true))"] do
    runQuery env "erased constant array model" s!"(set-logic ALL) {input} (check-sat)" fun query =>
      checkArrayRefutation query q(∀ (A : Type) (read : A → Int → Int)
        (write : A → Int → Int → A) (const : Int → A),
        (arrayLaws Int Int A read write ∧ (∀ v i, read (const v) i = v)) → True → False)
  runQuery env "constant array only in an ignored pattern" "
    (set-logic ALL)
    (assert (forall ((i Int)) (! (= i i)
      :pattern ((select ((as const (Array Int Int)) 0) i)))))
    (check-sat)" fun query =>
      checkArrayRefutation query q((∀ i : Int, i = i) → False)

private def checkHorn (env : Environment) : IO Unit := do
  let check (path : String) (expected : Expr) : IO Unit := do
    (parseAndInspectQuery (← IO.FS.readFile path) (name := path) (mode := .chc) fun query => do
      let problem ← Smt2Lean.Chc.validateQuery query
      let action : MetaM Unit := do
        checkStatement query (← defineProblem problem) expected .problem
      discard <| action.toIO { fileName := path, fileMap := default } { env }
    ).runIO
  check "tests/translation/chc/arrays.smt2" q(
    ∃ (A : Type) (readA : A → Int → Int) (writeA : A → Int → Int → A)
      (N : Type) (readN : N → Int → A) (writeN : N → Int → A → N)
      (R : A → Int → Prop) (Rows : N → Prop),
      arrayLaws Int Int A readA writeA ∧ arrayLaws Int A N readN writeN ∧
      (∀ a : A, R a 0) ∧
      (∀ (a : A) (i : Int), R a i → R (writeA a i i) (i + 1)) ∧
      (∀ (a : A) (i : Int), R a i → readA (writeA a i i) i ≠ i → False) ∧
      (∀ a : N, Rows a) ∧ (∀ (a : N) (r : A), Rows a → Rows (writeN a 0 r)))
  check "tests/translation/chc/array-constants.smt2" q(
    ∃ (A : Type) (read : A → Int → Int) (write : A → Int → Int → A)
      (const : Int → A) (R : A → Prop),
      arrayLaws Int Int A read write ∧ (∀ v i, read (const v) i = v) ∧
      R (const 0) ∧
      (∀ a : A, R a → R (write a 0 0)) ∧
      (∀ a : A, R a → read a 0 ≠ 0 → False) ∧
      (∀ v : Int, v = 0 → R (const v)))

def main : IO Unit := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules #[{ module := `Smt2Lean.Translate },
    { module := `tests.backend.ArrayModel }] {} (loadExts := true)
  checkBasic env
  checkUnused env
  checkSorts env
  checkIsolation env
  checkQuantified env
  checkConstants env
  checkHorn env
  IO.println "Arrays passed: flat/nested/quantified/constant arrays, CHC models, exact targets, countermodel, and standalone emission"
