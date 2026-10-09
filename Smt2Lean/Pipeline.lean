import Smt2Lean.Translate
import Smt2Lean.Emit
import Smt2Lean.Fixedpoint

namespace Smt2Lean.Pipeline

open Lean Meta Emit

/-- Explicit consumer profiles; auto retains the existing strict HORN behavior. -/
inductive Mode where
  | auto | model | fixedpoint
  deriving BEq

/-- Reconstruct at each check, but return output only after the entire session succeeds.
`maxRecDepth` sets the recursion limit during translation and in the generated Lean file. -/
def translateSession (input : String) (env : Environment) (name : String := "session")
    (maxRecDepth : Nat := Emit.defaultMaxRecDepth) (mode : Mode := .auto) : IO String := do
  let adapted ← if mode == .fixedpoint then
    match Fixedpoint.adapt input name with
    | .ok script => pure script
    | .error message => throw (IO.userError message)
    else pure ({ text := input } : Fixedpoint.Script)
  let state ← IO.mkRef ({ env } : Core.State)
  let skipped ← IO.mkRef adapted.skipped
  let goals ← IO.mkRef (#[] : Array Goal)
  let context : Core.Context := {
    fileName := name, fileMap := default
    options := Lean.maxRecDepth.set {} maxRecDepth
    maxRecDepth }
  (Backend.parseAndInspectSession adapted.text (name := name) (mode := .auto)
      (sources := adapted.sources)
      (onSkipped := fun command => skipped.modify (·.push command)) fun query => do
    let problem? ← if mode == .fixedpoint then some <$> Fixedpoint.validate query
      else if mode == .auto && query.logic == some "HORN" then
        some <$> Chc.validateQuery query name else pure none
    let action : MetaM Goal := do
      if mode == .fixedpoint then
        Arithmetic.withZeroCases query.assertionTerms fun parameters _ => do
          unless parameters.isEmpty do
            throwError "fixedpoint: division/modulus requires a nonzero literal divisor; underspecified background functions are unsupported"
      let (statement, kind) ← match problem? with
        | some problem => do
          let stem := if mode == .fixedpoint then "Safe" else "Problem"
          let statement ← Translate.problemStatement problem (.mkSimple s!"{stem}_{query.number}")
          let assertionCount := query.assertions.size - query.assumptionCount
          let parts := statement.parts.mapIdx fun i part => Id.run do
            let some clause := problem.clauses[i]? | return part
            if clause.assertionNumber > assertionCount then
              return { part with label := s!"assumption {clause.assertionNumber - assertionCount}" }
            else return part
          pure ({ statement with parts }, if mode == .fixedpoint then .safety else .problem)
        | none => do
          if mode == .model then
            pure (← Translate.modelStatement query (.mkSimple s!"Model_{query.number}"), .model)
          else pure (← Translate.refutationStatement query (.mkSimple s!"Refutation_{query.number}"), .refutation)
      return {
        value := statement.value, parts := statement.parts, definitions := statement.definitions
        kind, source := query.source, assertions := query.assertionSources
        checkCommand := if mode == .fixedpoint then "query" else query.checkCommand, assumptionCount := query.assumptionCount }
    let (goal, checkedState, _) ← action.toIO context (← state.get)
    state.set checkedState
    goals.modify (·.push goal)
  ).runIO
  let (source, _, _) ← (renderSession (← goals.get) (← skipped.get) maxRecDepth).toIO context (← state.get)
  return source

end Smt2Lean.Pipeline
