import Smt2Lean.Translate

namespace Smt2Lean.Emit

open Lean Meta

/-- Select the proposition and proof template to emit. -/
inductive GoalKind where
  | refutation
  | problem

private def sourceComment (label : String) (source : Source.Ref) : String :=
  let span := source.span
  -- Quote the filename so a newline in a path cannot escape the Lean comment.
  s!"-- Source: {reprStr source.file}:{span.start.line}:{span.start.column}-" ++
  s!"{span.stop.line}:{span.stop.column} ({label}, command {source.number})\n"

/-- Render one file with statements first, followed by unfinished proofs. -/
def render (value : Expr) (kind : GoalKind := .refutation)
    (source : Option Source.Ref := none) (assertions : Array Source.Ref := #[]) : MetaM String := do
  let (definitionName, theoremName, description, proofTarget) := match kind with
    | .refutation => ("Refutation", "refutation",
        "No interpretation satisfies all assertions of the SMT query.", "the query's refutation")
    | .problem => ("Problem", "problem",
        "There are relation interpretations satisfying every Horn clause.",
        "the existence of satisfying relations")
  -- lean-smt's Int.abs is not in Lean core; emit its if/then/else definition.
  let value ← deltaExpand value (· == ``Int.abs)
  let body ← withOptions (fun options => options
      |>.setBool `pp.fullNames true
      |>.setBool `pp.deepTerms true
      |>.setBool `pp.proofs true
      -- Unused existential variables still need explicit types in emitted source.
      |>.setBool `pp.funBinderTypes true
      -- Without annotations, a closed equality such as 1 = 2 defaults to Nat.
      |>.setBool `pp.numericTypes true
      |> (pp.maxSteps.set · 1000000)) do
    return (← ppExpr value).pretty
  if body.contains "⋯" then
    throwError "proposition is too large to print completely"
  let label := match kind with
    | .refutation => "assertion"
    | .problem => "clause"
  let provenance := source.map (sourceComment "check-sat") |>.getD ""
  let provenance := provenance ++ String.join
    (assertions.mapIdx (fun i ref => sourceComment s!"{label} {i + 1}" ref)).toList
  let statements := "import Init\n\n-- Statements\n\n" ++
    provenance ++
    s!"/-- {description} -/\n" ++
    s!"def {definitionName} : Prop :=\n  " ++ body.replace "\n" "\n  " ++ "\n"
  let proofs := "\n-- Proofs\n\n" ++
    s!"-- Unfinished proof: replace sorry to establish {proofTarget}.\n" ++
    s!"theorem {theoremName} : {definitionName} := by\n  sorry\n"
  return statements ++ proofs

/-- Write Query.lean in a new directory. Existing destinations are refused. -/
def writeFile (output : System.FilePath) (source : String) : IO Unit := do
  try
    IO.FS.createDir output
  catch
    | .alreadyExists .. => throw (IO.userError s!"output already exists: {output}")
    | error => throw error
  IO.FS.writeFile (output / "Query.lean") source

end Smt2Lean.Emit
