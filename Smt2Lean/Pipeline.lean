import Smt2Lean.Translate
import Smt2Lean.Emit

namespace Smt2Lean.Pipeline

open Lean Meta Emit

/-- Reconstruct at each check, but return output only after the entire session succeeds.
`maxRecDepth` sets the recursion limit during translation and in the generated Lean file. -/
def translateSession (input : String) (env : Environment) (name : String := "session")
    (maxRecDepth : Nat := Emit.defaultMaxRecDepth) : IO String := do
  let state ← IO.mkRef ({ env } : Core.State)
  let skipped ← IO.mkRef (#[] : Array Source.Command)
  let goals ← IO.mkRef (#[] : Array Goal)
  let context : Core.Context := {
    fileName := name, fileMap := default
    options := Lean.maxRecDepth.set {} maxRecDepth
    maxRecDepth }
  (Backend.parseAndInspectSession input (name := name) (mode := .auto)
      (onSkipped := fun command => skipped.modify (·.push command)) fun query => do
    let problem? ← if query.logic == some "HORN" then
      some <$> Chc.validateQuery query name else pure none
    let action : MetaM Goal := do
      let (statement, kind) ← match problem? with
        | some problem => do
          let statement ← Translate.problemStatement problem (.mkSimple s!"Problem_{query.number}")
          let assertionCount := query.assertions.size - query.assumptionCount
          let parts := statement.parts.mapIdx fun i part => Id.run do
            let some clause := problem.clauses[i]? | return part
            if clause.assertionNumber > assertionCount then
              return { part with label := s!"assumption {clause.assertionNumber - assertionCount}" }
            else return part
          pure ({ statement with parts }, .problem)
        | none => do
          pure (← Translate.refutationStatement query (.mkSimple s!"Refutation_{query.number}"), .refutation)
      return {
        value := statement.value, parts := statement.parts, definitions := statement.definitions
        kind, source := query.source, assertions := query.assertionSources
        checkCommand := query.checkCommand, assumptionCount := query.assumptionCount }
    let (goal, checkedState, _) ← action.toIO context (← state.get)
    state.set checkedState
    goals.modify (·.push goal)
  ).runIO
  let (source, _, _) ← (renderSession (← goals.get) (← skipped.get) maxRecDepth).toIO context (← state.get)
  return source

end Smt2Lean.Pipeline
