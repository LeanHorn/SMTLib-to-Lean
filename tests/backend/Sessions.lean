import tests.backend.Support

open Lean Meta Qq Classical
open Smt2Lean.Backend Smt2Lean.Translate Smt2Lean.Emit

open Smt2Lean.Tests

namespace Smt2Lean.Tests

local notation "smtDiv" => (fun (zero : Int → Int) (x y : Int) => ite (y = 0) (zero x) (x / y))
local notation "smtMod" => (fun (zero : Int → Int) (x y : Int) => ite (y = 0) (zero x) (x % y))

local notation "exclusive" => (fun p q : Prop => (p ∧ ¬q) ∨ (¬p ∧ q))

def checkSessions (env : Environment) : IO Unit := do
  runQuery env "colliding-function-bindings" "
    (set-logic ALL)
    (declare-fun set.card (Int) Int)
    (declare-const x Int)(declare-const |smt2lean.collision.0.0| Int)
    (define-fun bump ((|set.card| Int)) Int (+ set.card 1))
    (assert (= (set.card x) (- 1)))
    (assert (= (|set.card| x) (set.card x)))
    (assert (forall ((set.card Int)) (= (bump set.card) (+ set.card 1))))
    (assert (let ((set.card 7) (y (set.card x))) (and (= set.card 7) (= y (- 1)))))
    (assert (forall ((true Int)) (= true true)))
    (assert (= |smt2lean.collision.0.0| |smt2lean.collision.0.0|))
    (check-sat)" fun query => do
      unless query.declarations.map (·.name) == #["set.card", "x", "smt2lean.collision.0.0"] &&
          query.commands[1]!.text == "(declare-fun set.card (Int) Int)" do
        throwError "collision adaptation lost original declaration names or commands"
      checkRefutation query q(∀ (f : Int → Int) (x collision : Int),
        f x = -1 ∧ f x = f x ∧ (∀ n : Int, n + 1 = n + 1) ∧
          ((7 : Int) = 7 ∧ f x = -1) ∧ (∀ n : Int, n = n) ∧ collision = collision → False)
  let collisionSession := "
    (set-logic ALL)(declare-const set.card Int)(assert (= set.card 0))(check-sat)
    (push 1)(define-fun f ((set.card Int)) Int (+ set.card 1))
    (check-sat-assuming ((= (f 0) 1)))(pop 1)(check-sat)
    (reset-assertions)(declare-const |set.card| Bool)(assert (not set.card))(check-sat)
    (reset)(set-option :global-declarations true)(set-logic ALL)
    (push 1)(declare-fun set.card (Int) Int)(assert (= (set.card 0) (- 1)))(pop 1)
    (check-sat-assuming ((= (set.card 0) (- 1))))
    (reset-assertions)(check-sat-assuming ((= (|set.card| 0) (- 1))))
    (reset)(set-logic ALL)(declare-const set.card Int)(assert (= set.card 1))(check-sat)"
  let collisionExpected := #[
    q(∀ c : Int, c = 0 → False),
    q(∀ c : Int, (c = 0 ∧ (0 : Int) + 1 = 1) → False),
    q(∀ c : Int, c = 0 → False), q(∀ c : Prop, ¬c → False),
    q(∀ f : Int → Int, f 0 = -1 → False), q(∀ f : Int → Int, f 0 = -1 → False),
    q(∀ c : Int, c = 1 → False)]
  let collisionIds ← IO.mkRef (#[] : Array Nat)
  (parseAndInspectSession collisionSession (name := "collision-session") fun query => do
    let #[declaration] := query.declarations | throw (.error "expected one colliding declaration")
    unless declaration.name == "set.card" do throw (.error "lost original declaration name")
    let index := (← collisionIds.get).size
    let some expected := collisionExpected[index]? | throw (.error "unexpected collision snapshot")
    collisionIds.modify (·.push declaration.term.getId!)
    discard <| (checkRefutation query expected).toIO
      { fileName := "collision-session", fileMap := default } { env }
  ).runIO
  let ids ← collisionIds.get
  unless ids.size == 7 && ids[0]! == ids[2]! && ids[0]! != ids[3]! &&
      ids[4]! == ids[5]! && ids[0]! != ids[6]! do
    throw (IO.userError "colliding declaration identities did not follow session lifetimes")
  let definitionTargets := #[q(∀ x : Int, x + (x + 1) = x + (x + 1) → False),
    q((-1 : Int) = -1 → False)]
  let definitionChecks ← IO.mkRef 0
  (parseAndInspectSession "
    (set-logic ALL)(declare-const x Int)
    (define-fun set.card ((n Int)) Int (+ x n))(define-const c Int (set.card 1))
    (assert (= (|set.card| c) (+ x (+ x 1))))(check-sat)
    (reset-assertions)(define-const set.card Int (- 1))
    (check-sat-assuming ((= |set.card| (- 1))))"
      (name := "colliding-definitions") fun query => do
    let index ← definitionChecks.get
    let names := if index == 0 then #["set.card", "c"] else #["set.card"]
    unless query.definitions.map (·.name) == names do
      throw (.error "lost original definition names after expansion or reset")
    let some expected := definitionTargets[index]? | throw (.error "unexpected definition snapshot")
    discard <| (checkRefutation query expected).toIO
      { fileName := "colliding-definitions", fileMap := default } { env }
    definitionChecks.modify (· + 1)
  ).runIO
  unless (← definitionChecks.get) == 2 do throw (IO.userError "missing definition snapshot")
  let base := q(∀ p : Prop, p → False)
  let integer := q(∀ (p : Prop) (x : Int), (p ∧ x + 1 > 0) → False)
  let conditional := q(∀ (p : Prop) (x : Int), (p ∧ (if p then x else -x) = x) → False)
  let fact := q(∃ p : Int → Prop, p 0)
  let cases : Array (String × String × Array Expr × Array Nat) := #[
    ("smt", "Refutation", #[base, integer,
      q(∀ (p : Prop) (x : Int) (q : Prop),
        (p ∧ x + 1 > 0 ∧ (q ∧ exclusive p q ∧ (x ≠ 0 ∧ x ≠ x + 1 ∧ 0 ≠ x + 1))) → False),
      integer, base,
      q(∀ p x : Prop, (p ∧ ¬x ∧ (¬x ∨ exclusive p x)) → False),
      conditional, conditional], #[7, 8]),
    ("sorts", "Refutation", #[
      q(∀ A : Type, Nonempty A → ∀ x : A, x = x → False),
      q(∀ A B : Type, Nonempty A → Nonempty B → ∀ (x : A) (y : B), (x = x ∧ y = y) → False),
      q(∀ A : Type, Nonempty A → ∀ x : A, x = x → False),
      q(∀ A B : Type, Nonempty A → Nonempty B → ∀ (x : A) (p : B → Prop),
        (x = x ∧ ∀ y : B, p y) → False),
      q(∀ A : Type, Nonempty A → (∀ _x : A, False) → False),
      q(∀ A : Type, Nonempty A → (∀ x : A, x = x) → False),
      q(∀ A : Type, Nonempty A → (∀ x : A, x = x) → False), q(True → False)], #[]),
    ("resets", "Refutation", #[
      q(∀ (p : Prop) (x : Int), (p ∧ x + 1 > 0 ∧ p) → False), q(True → False),
      q(∀ p : Int, p = 1 → False), q(∀ p : Prop, ¬p → False),
      q(∀ _p : Prop, True → False), q(∀ (p : Prop) (_x : Int), ¬p → False), q(True → False)], #[]),
    ("assuming", "Refutation", #[q(∀ p : Prop, (p ∧ ¬p) → False), base, base,
      q(∀ p : Prop, (p ∧ p ∧ p ∧ p) → False),
      q(∀ p q : Prop, (p ∧ q ∧ ¬p) → False), q(∀ (p : Prop) (_q : Int), p → False)], #[]),
    ("compatibility", "Refutation", #[
      q(∀ (x : Int) (p : Prop) (_quoted : Int),
        (x + 1 = x + 1 ∧ ((p ∧ x + 1 > x) ∧ x + 1 = x + 1) ∧ (9 : Int) = 9) → False),
      q(∀ (x : Int) (_p : Prop) (_quoted : Int), x + 1 = x + 1 → False),
      q(∀ (x : Int) (_p : Prop) (quoted : Int), (x + 1 = x + 1 ∧ quoted = quoted) → False),
      q(∀ (x : Int) (_p : Prop) (_quoted : Int), x + 1 = x + 1 → False),
      q(¬True → False), q(True → False), q((7 : Int) = 7 → False)], #[]),
    ("chc", "Problem", #[fact,
      q(∃ (p : Int → Prop) (r : Int → Prop → Prop),
        p 0 ∧ (∀ x : Int, p x → x > 0 → r (x + 1) True)),
      q(∃ (p : Int → Prop) (r : Int → Prop → Prop) (done : Prop),
        p 0 ∧ (∀ x : Int, p x → x > 0 → r (x + 1) True) ∧
          (∀ x : Int, r x True → done)),
      fact,
      q(∃ (p : Int → Prop) (r : Prop → Prop), p 0 ∧ (∀ b : Prop, b → r b)),
      fact], #[])
  ]
  for (fixture, baseName, expected, classicalQueries) in cases do
    let path := s!"tests/translation/sessions/{fixture}.smt2"
    let source ← Smt2Lean.Pipeline.translateSession (← IO.FS.readFile path) env path
    let [statements, proofs] := source.splitOn "-- Proofs\n"
      | throw (IO.userError "wrong session layout")
    unless !statements.contains "sorry" && !proofs.contains "def " &&
        (List.range expected.size).all (fun i => statements.contains s!"def {baseName}_{i + 1} : Prop") &&
        (proofs.splitOn "theorem ").length == expected.size + 1 do
      throw (IO.userError "wrong session statement/proof count")
    if fixture == "smt" then
      for helper in #["SMT.xor", "SMT.distinct3"] do
        unless (statements.splitOn s!"def {helper}").length == 2 do
          throw (IO.userError "session helpers must be emitted once")
    unsafe enableInitializersExecution
    let some emitted ← Elab.runFrontend source
        (({} : Options).setBool `Elab.async false) "Query.lean" `Query
      | throw (IO.userError "session did not elaborate")
    let check : MetaM Unit := do
      for i in [:expected.size] do
        let name := Name.mkSimple s!"{baseName}_{i + 1}"
        let proofName := Name.mkSimple s!"{baseName.toLower}_{i + 1}"
        let .defnInfo definition ← getConstInfo name | throwError "missing {name}"
        if definition.value.hasFVar || definition.value.hasMVar || definition.value.hasLooseBVars then
          throwError "{name} contains unresolved variables"
        checkEqual definition.type q(Prop)
        let value ← deltaExpand definition.value Smt2Lean.Helpers.isHelper
        checkEqual value expected[i]!
        checkAxioms name (classicalQueries.contains (i + 1))
        let .thmInfo proof ← getConstInfo proofName | throwError "missing {proofName}"
        unless proof.type == mkConst name do throwError "wrong proof target for {name}"
        let axioms ← collectAxioms proofName
        let statementAxioms ← collectAxioms name
        unless axioms.contains ``sorryAx && axioms.size == statementAxioms.size + 1 &&
            statementAxioms.all axioms.contains do
          throwError "unexpected proof axioms for {name}"
        unless statements.contains s!"(query {i + 1}: check-sat" do
          throwError "missing query source for {name}"
    discard <| check.toIO { fileName := path, fileMap := default } { env := emitted }
  let source ← Smt2Lean.Pipeline.translateSession
    "(set-logic ALL)(check-sat)(push 1)(assert (= (div 1 0) 7))(check-sat)\
     (push 1)(assert (= (mod 1 0) 3))(check-sat)(pop 2)(check-sat)\
     (reset)(set-logic HORN)(assert (=> (= (div 1 0) 7) false))(check-sat)" env
  unsafe enableInitializersExecution
  let some emitted ← Elab.runFrontend source
      (({} : Options).setBool `Elab.async false) "Query.lean" `Query
    | throw (IO.userError "division session did not elaborate")
  let check : MetaM Unit := do
    for (name, expected) in #[
      (`Refutation_1, q(True → False)),
      (`Refutation_2, q(∀ d : Int → Int, smtDiv d 1 0 = 7 → False)),
      (`Refutation_3, q(∀ d m : Int → Int, (smtDiv d 1 0 = 7 ∧ smtMod m 1 0 = 3) → False)),
      (`Refutation_4, q(True → False)),
      (`Problem_5, q(∃ d : Int → Int, smtDiv d 1 0 = 7 → False))
    ] do
      let .defnInfo definition ← getConstInfo name | throwError "missing {name}"
      checkEqual (← deltaExpand definition.value Smt2Lean.Helpers.isHelper) expected
      checkStatementAxioms name
  discard <| check.toIO { fileName := "division session", fileMap := default } { env := emitted }
  runQuery env "define-const-equivalence" "
    (set-logic ALL)(declare-const x Int)
    (define-const c Int (+ x 1))(define-fun f () Int (+ x 1))
    (define-const b Bool (> c x))(define-fun g () Bool (> f x))
    (assert (= c f))(check-sat-assuming ((= b g)))" fun query => do
      unless query.definitions.size == 4 && query.assumptionCount == 1 &&
          query.commands[2]!.text.contains "define-const" &&
          !query.invoked.contains "check-sat-assuming" do
        throwError "constant definitions or source command identity were lost"
      checkRefutation query q(∀ x : Int, (x + 1 = x + 1 ∧ (x + 1 > x) = (x + 1 > x)) → False)
  runQuery env "assuming-quantified-definition" "
    (set-logic ALL)(declare-const x Int)
    (define-const b Bool (forall ((y Int)) (>= (+ y x) y)))
    (check-sat-assuming (b (let ((z x)) (= z x)) true))" fun query =>
      checkRefutation query q(∀ x : Int, ((∀ y : Int, y + x ≥ y) ∧ x = x ∧ True) → False)
  runQuery env "assuming-constant-array" "
    (set-logic ALL)(declare-const x Int)
    (define-const a (Array Int Int) ((as const (Array Int Int)) x))
    (check-sat-assuming ((= (select a 0) x)
      (= (select ((as const (Array Int Int)) (+ x 1)) 2) (+ x 1))))" fun query => do
      unless query.declarations.map (·.name) == #["x"] && query.assumptionCount == 2 &&
          query.assertions.all (fun assertion => !assertion.arrayConstants.isEmpty) do
        throwError "constant-array assumptions lost their private constructor requirements"
      let value ← defineRefutation query
      checkStatementAxioms `Refutation
      checkEmission value
  for input in #[
    "(set-logic ALL)(push 1)(define-const c Int 1)(pop 1)(check-sat-assuming ((= c 1)))",
    "(set-logic ALL)(define-const c Int 1)(reset-assertions)(check-sat-assuming ((= c 1)))",
    "(set-logic ALL)(define-const c Int 1)(reset)(set-logic ALL)(check-sat-assuming ((= c 1)))",
    "(set-logic ALL)(check-sat-assuming ((! true :named leaked)))",
    "(set-logic ALL)(define-const s String \"unsupported\")(check-sat)"] do
    match ← (parseAndInspectSession input (fun _ => pure ())).run with
    | .ok _ => throw (IO.userError "accepted an out-of-scope or unsupported constant/assumption")
    | .error _ => pure ()
  IO.println "Session translation passed: SMT/CHC goals match handwritten propositions"

end Smt2Lean.Tests
