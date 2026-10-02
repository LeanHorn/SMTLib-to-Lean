import Smt2Lean.Source
import Smt2Lean.Emit.Datatype
import Smt2Lean.Theory.Helpers
import Smt.Reconstruct.Int.Core
import Mathlib.Algebra.Order.Floor.Defs

namespace Smt2Lean.Emit

open Lean Meta

/-- Recursion limit for checking generated Lean files. -/
def defaultMaxRecDepth : Nat := 4096

/-- Select the proposition and proof template to emit. -/
inductive GoalKind where
  | refutation
  | problem

/-- A closed, checked proposition and its source locations. Contains no native terms. -/
structure Goal where
  value : Expr
  checkCommand : String := "check-sat"
  assumptionCount : Nat := 0
  kind : GoalKind := .refutation
  source : Option Source.Ref := none
  assertions : Array Source.Ref := #[]

private def sourceComment (label : String) (source : Source.Ref) : String :=
  let span := source.span
  -- Quote filenames and names so newlines cannot escape the Lean comment.
  s!"-- Source: {reprStr source.file}:{span.start.line}:{span.start.column}-" ++
  s!"{span.stop.line}:{span.stop.column} ({label}, command {source.number}){source.namedContext}\n"

private def printExpr (value : Expr) : MetaM String := do
  let value ← Datatypes.showParameters value
  let body ← withOptions (fun options => options
      |>.setBool `pp.fullNames true
      |>.setBool `pp.deepTerms true
      |>.setBool `pp.proofs true
      |>.setBool `pp.funBinderTypes true
      |>.setBool `pp.numericTypes true
      -- Floor is polymorphic: an untyped ↑i could re-elaborate at Int instead of Real.
      |>.setBool `pp.coercions.types true
      |> (pp.maxSteps.set · 1000000)) do
    return (← ppExpr value).pretty
  if body.contains "⋯" then
    throwError "proposition is too large to print completely"
  return body

/-- Print the checked helper itself, so its meaning is not duplicated in a template. -/
private def renderHelper (name : Name) : MetaM String := do
  let .defnInfo definition ← getConstInfo name
    | throwError "expected an operator definition: {name}"
  lambdaTelescope definition.value fun parameters body => do
    let binders ← parameters.mapM fun parameter => do
      let localDecl ← parameter.fvarId!.getDecl
      let binder := s!"{← printExpr parameter} : {← printExpr localDecl.type}"
      return if localDecl.binderInfo.isImplicit then "{" ++ binder ++ "}" else "(" ++ binder ++ ")"
    let universes := if definition.levelParams.isEmpty then "" else
      ".{" ++ String.intercalate ", " (definition.levelParams.map toString) ++ "}"
    let keyword := if name == `SMT.realDiv then "noncomputable def" else "def"
    return s!"{keyword} {name}{universes} " ++ String.intercalate " " binders.toList ++
      s!" : {← printExpr (← inferType body)} :=\n  " ++ (← printExpr body).replace "\n" "\n  " ++ "\n\n"

private def renderGoal (goal : Goal) (number : Option Nat) : MetaM (String × String) := do
  let (baseName, baseProof, description, proofTarget) := match goal.kind with
    | .refutation => ("Refutation", "refutation",
        "No interpretation satisfies all assertions of the SMT query.", "the query's refutation")
    | .problem => ("Problem", "problem",
        "There are relation interpretations satisfying every Horn clause.",
        "the existence of satisfying relations")
  let suffix := number.map (fun n => s!"_{n}") |>.getD ""
  let definitionName := baseName ++ suffix
  let theoremName := baseProof ++ suffix
  -- lean-smt's Int.abs is not in Lean core; emit its if/then/else definition.
  let value ← deltaExpand goal.value (· == ``Int.abs)
  let needsClassical := (value.find? (·.isConstOf ``Classical.propDecidable)).isSome
  let body ← printExpr value
  let label := match goal.kind with
    | .refutation => "assertion"
    | .problem => "clause"
  let queryLabel := number.map (fun n => s!"query {n}: ") |>.getD ""
  let provenance := goal.source.map (sourceComment (queryLabel ++ goal.checkCommand)) |>.getD ""
  let provenance := provenance ++ String.join
    (goal.assertions.mapIdx (fun i ref => sourceComment (if i < goal.assertions.size - goal.assumptionCount then s!"{queryLabel}{label} {i + 1}"
        else s!"{queryLabel}assumption {i + 1 - (goal.assertions.size - goal.assumptionCount)}") ref)).toList
  let definition := if needsClassical then
    s!"noncomputable def {definitionName} : Prop := by\n  classical\n  exact\n    " ++
      body.replace "\n" "\n    " ++ "\n"
    else s!"def {definitionName} : Prop :=\n  " ++ body.replace "\n" "\n  " ++ "\n"
  let statement := provenance ++ s!"/-- {description} -/\n" ++ definition
  let proof := s!"-- Unfinished proof: replace sorry to establish {proofTarget}.\n" ++
    s!"theorem {theoremName} : {definitionName} := by\n  sorry\n"
  return (statement, proof)

/-- Emit helpers once, then all statements, then all unfinished proofs.
Single-query files retain their original names and formatting. -/
def renderSession (goals : Array Goal) (skipped : Array Source.Command := #[])
    (maxRecDepth : Nat := defaultMaxRecDepth) : MetaM String := do
  if goals.isEmpty then throwError "expected at least one translated query"
  let datatypeGroups ← Datatypes.groups (goals.map (·.value))
  let datatypeDeclarations ← Datatypes.render datatypeGroups printExpr
  let mut helpers : Array Name := #[]
  for goal in goals do
    for name in goal.value.getUsedConstants.filter Helpers.isHelper do
      unless helpers.contains name do helpers := helpers.push name
  let helperDefinitions := String.join (← (helpers.qsort Name.lt).toList.mapM renderHelper)
  let entries ← goals.mapIdxM fun i goal =>
    renderGoal goal (if goals.size == 1 then none else some (i + 1))
  let requests := String.join (skipped.toList.map fun command =>
    sourceComment "unexecuted request" command.source ++ s!"-- Not executed: {reprStr command.text}\n")
  let usesReal := (← Datatypes.usesReal datatypeGroups) || goals.any fun goal => (goal.value.find? (·.isConstOf ``Real)).isSome
  let usesFloor := goals.any fun goal => (goal.value.find? (·.isConstOf ``Int.floor)).isSome
  let imports := if usesFloor then "import Mathlib.Algebra.Order.Archimedean.Real.Basic"
    else if usesReal then "import Mathlib.Data.Real.Basic" else "import Init"
  return imports ++ s!"\n\nset_option maxRecDepth {maxRecDepth}\n\n-- Statements\n\n" ++
    requests ++ datatypeDeclarations ++ helperDefinitions ++
    String.intercalate "\n" (entries.toList.map Prod.fst) ++ "\n-- Proofs\n\n" ++
    String.intercalate "\n" (entries.toList.map Prod.snd)

/-- Render one file with statements first, followed by unfinished proofs. -/
def render (value : Expr) (kind : GoalKind := .refutation)
    (source : Option Source.Ref := none) (assertions : Array Source.Ref := #[])
    (maxRecDepth : Nat := defaultMaxRecDepth) : MetaM String :=
  renderSession #[{ value, kind, source, assertions }] (maxRecDepth := maxRecDepth)

/-- Write Query.lean in a new directory. Existing destinations are refused. -/
def writeFile (output : System.FilePath) (source : String) : IO Unit := do
  try
    IO.FS.createDir output
  catch
    | .alreadyExists .. => throw (IO.userError s!"output already exists: {output}")
    | error => throw error
  IO.FS.writeFile (output / "Query.lean") source

end Smt2Lean.Emit
