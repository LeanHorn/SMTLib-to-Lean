import Smt2Lean.Translate
import Smt2Lean.Emit

namespace Smt2Lean.Pipeline

open Lean Meta Emit

/-- Reconstruct at each check, but return output only after the entire session succeeds. -/
def translateSession (input : String) (env : Environment) (name : String := "session") : IO String := do
  let state ← IO.mkRef ({ env } : Core.State)
  let goals ← IO.mkRef (#[] : Array Goal)
  let context : Core.Context := { fileName := name, fileMap := default }
  (Backend.parseAndInspectSession input (name := name) (mode := .auto) fun query => do
    let problem? ← if query.logic == some "HORN" then
      some <$> Chc.validateQuery query name else pure none
    let action : MetaM Goal := do
      let (value, kind) ← match problem? with
        | some problem => do
          pure (← Translate.defineProblem problem (.mkSimple s!"Problem_{query.number}"), .problem)
        | none => do
          pure (← Translate.defineRefutation query (.mkSimple s!"Refutation_{query.number}"), .refutation)
      return {
        value, kind, source := query.source, assertions := query.assertionSources
        checkCommand := query.checkCommand, assumptionCount := query.assumptionCount }
    let (goal, checkedState, _) ← action.toIO context (← state.get)
    state.set checkedState
    goals.modify (·.push goal)
  ).runIO
  let (source, _, _) ← (renderSession (← goals.get)).toIO context (← state.get)
  return source

end Smt2Lean.Pipeline
