import tests.backend.Support

open Lean Meta Qq Classical
open Smt2Lean.Backend Smt2Lean.Translate Smt2Lean.Emit

open Smt2Lean.Tests

namespace Smt2Lean.Tests

local notation "smtDiv" => (fun (zero : Int → Int) (x y : Int) => ite (y = 0) (zero x) (x / y))
local notation "smtMod" => (fun (zero : Int → Int) (x y : Int) => ite (y = 0) (zero x) (x % y))

local notation "exclusive" => (fun p q : Prop => (p ∧ ¬q) ∨ (¬p ∧ q))

def checkSessions (env : Environment) : IO Unit := do
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
        (statements.splitOn s!"def {baseName}_").length == expected.size + 1 &&
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
  IO.println "Session translation passed: SMT/CHC goals match handwritten propositions"

end Smt2Lean.Tests
