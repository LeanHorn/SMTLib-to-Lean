import Smt2Lean.Emit
import Lean.Elab.Frontend

open Lean Meta Elab Term Qq

run_elab do
  for expected in #[
      q(∀ a b c : Prop, (a → b) ∧ (b → c)),
      q(∀ a b c : Prop, a ∧ ((a → b) ∧ (b → c))),
      q(∀ a b : Prop, a ∧ (∀ x : Int, x = 0 → b)),
      q(∀ a b : Prop, a ∧ (∃ x : Int, x = 0 ∧ b))] do
    let source ← Smt2Lean.Emit.render expected .problem
      (parts := #[{ name := `Grouping, value := expected, label := "clause" }])
    let statements := (source.splitOn "-- Proofs\n").head!
    unsafe enableInitializersExecution
    let some environment ← Elab.runFrontend statements {} "Emitted.lean" `Emitted
      | throwError "emitted statement did not elaborate"
    let some (.defnInfo definition) := environment.find? `Problem
      | throwError "emitted Problem is missing"
    unless ← withEnv environment (isDefEq definition.value expected) do
      throwError "emission changed connective grouping: {definition.value}\nexpected {expected}"
