import Smt2Lean.Source
import Smt2Lean.Statement
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
  parts : Array StatementPart := #[]
  definitions : Array StatementPart := #[]
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

private def binderName (name : Name) (body : Expr) : MetaM Name := do
  let name := name.eraseMacroScopes
  getUnusedUserName (if body.hasLooseBVar 0 then name else Name.mkSimple ("_" ++ name.toString))

/-- Print logical spines at one indentation level. Parentheses preserve grouping;
ordinary term formatting still handles lets, matches, and operator precedence. -/
private partial def printProposition (value : Expr) : MetaM String := do
  match value with
  | .forallE name type body info =>
    if value.isArrow && (← isProp type) then
      return s!"({← printProposition type}) →\n{← printProposition (body.instantiate1 qPlaceholder)}"
    else
      withLocalDecl (← binderName name body) info type fun x => do
        return s!"∀ ({← printExpr x} : {← printExpr type}),\n{← printProposition (body.instantiate1 x)}"
  | _ =>
    if value.isAppOfArity ``Exists 2 then
      let predicate := value.appArg!
      if let .lam name type body info := predicate then
        return ← withLocalDecl (← binderName name body) info type fun x => do
          return s!"∃ ({← printExpr x} : {← printExpr type}),\n{← printProposition (body.instantiate1 x)}"
    if value.isAppOfArity ``And 2 then
      return s!"({← printProposition value.appFn!.appArg!}) ∧\n{← printProposition value.appArg!}"
    printExpr value
where
  -- An arrow's body does not refer to its proof binder.
  qPlaceholder := mkConst ``True.intro

private def definitionBody (value : Expr) : MetaM String := do
  let value ← deltaExpand value (· == ``Int.abs)
  let body ← printProposition value
  if (value.find? (·.isConstOf ``Classical.propDecidable)).isSome then
    return " by\n  classical\n  exact\n    " ++ body.replace "\n" "\n    "
  return "\n  " ++ body.replace "\n" "\n  "

/-- Open definition parameters with printable, distinct names, including dependent types. -/
private partial def withPrintedParameters (value : Expr)
    (inspect : Array Expr → Expr → MetaM String) (parameters : Array Expr := #[]) : MetaM String := do
  match value with
  | .lam name type body info =>
    withLocalDecl (← getUnusedUserName name.eraseMacroScopes) info type fun x =>
      withPrintedParameters (body.instantiate1 x) inspect (parameters.push x)
  | _ => inspect parameters value

private def renderPart (part : StatementPart) : MetaM String :=
  withPrintedParameters part.value fun parameters body => do
    let binders ← parameters.mapM fun x =>
      return s!"({← printExpr x} : {← printExpr (← inferType x)})"
    let provenance := part.source.map (sourceComment part.label) |>.getD ""
    let keyword := if part.label == "definition" || (body.find? (·.isConstOf ``Classical.propDecidable)).isSome then
      "noncomputable def" else "def"
    return provenance ++ s!"{keyword} {part.name}" ++
      String.join (binders.toList.map ("\n    " ++ ·)) ++
      s!" : {← printExpr (← inferType body)} :={← definitionBody body}\n\n"

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
  let body ← if goal.parts.isEmpty then printExpr value else printProposition value
  let label := match goal.kind with
    | .refutation => "assertion"
    | .problem => "clause"
  let queryLabel := number.map (fun n => s!"query {n}: ") |>.getD ""
  let provenance := goal.source.map (sourceComment (queryLabel ++ goal.checkCommand)) |>.getD ""
  let provenance := provenance ++ (if !goal.parts.isEmpty then "" else String.join
    (goal.assertions.mapIdx (fun i ref => sourceComment (if i < goal.assertions.size - goal.assumptionCount then s!"{queryLabel}{label} {i + 1}"
        else s!"{queryLabel}assumption {i + 1 - (goal.assertions.size - goal.assumptionCount)}") ref)).toList)
  let definition := if needsClassical then
    s!"noncomputable def {definitionName} : Prop := by\n  classical\n  exact\n    " ++
      body.replace "\n" "\n    " ++ "\n"
    else s!"def {definitionName} : Prop :=\n  " ++ body.replace "\n" "\n  " ++ "\n"
  let parts := String.join (← (goal.definitions ++ goal.parts).toList.mapM renderPart)
  let statement := parts ++ provenance ++ s!"/-- {description} -/\n" ++ definition
  let proof := s!"-- Unfinished proof: replace sorry to establish {proofTarget}.\n" ++
    s!"theorem {theoremName} : {definitionName} := by\n  sorry\n"
  return (statement, proof)

/-- Emit helpers once, then all statements, then all unfinished proofs.
Single-query files retain their original goal names. -/
def renderSession (goals : Array Goal) (skipped : Array Source.Command := #[])
    (maxRecDepth : Nat := defaultMaxRecDepth) : MetaM String := do
  if goals.isEmpty then throwError "expected at least one translated query"
  let values := goals.flatMap fun goal => #[goal.value] ++ (goal.definitions ++ goal.parts).map (·.value)
  let datatypeGroups ← Datatypes.groups values
  let datatypeDeclarations ← Datatypes.render datatypeGroups printExpr
  let mut helpers : Array Name := #[]
  for value in values do
    for name in value.getUsedConstants.filter Helpers.isHelper do
      unless helpers.contains name do helpers := helpers.push name
  let helperDefinitions := String.join (← (helpers.qsort Name.lt).toList.mapM renderHelper)
  let entries ← goals.mapIdxM fun i goal =>
    renderGoal goal (if goals.size == 1 then none else some (i + 1))
  let requests := String.join (skipped.toList.map fun command =>
    sourceComment "unexecuted request" command.source ++ s!"-- Not executed: {reprStr command.text}\n")
  let usesReal := (← Datatypes.usesReal datatypeGroups) || values.any fun value => (value.find? (·.isConstOf ``Real)).isSome
  let usesFloor := values.any fun value => (value.find? (·.isConstOf ``Int.floor)).isSome
  let imports := if usesFloor then "import Mathlib.Algebra.Order.Archimedean.Real.Basic"
    else if usesReal then "import Mathlib.Data.Real.Basic" else "import Init"
  return imports ++ s!"\n\nset_option maxRecDepth {maxRecDepth}\n\n-- Statements\n\n" ++
    requests ++ datatypeDeclarations ++ helperDefinitions ++
    String.intercalate "\n" (entries.toList.map Prod.fst) ++ "\n-- Proofs\n\n" ++
    String.intercalate "\n" (entries.toList.map Prod.snd)

/-- Render one file with statements first, followed by unfinished proofs. -/
def render (value : Expr) (kind : GoalKind := .refutation)
    (source : Option Source.Ref := none) (assertions : Array Source.Ref := #[])
    (maxRecDepth : Nat := defaultMaxRecDepth) (parts : Array StatementPart := #[])
    (definitions : Array StatementPart := #[]) : MetaM String :=
  renderSession #[{ value, parts, definitions, kind, source, assertions }] (maxRecDepth := maxRecDepth)

/-- Write Query.lean in a new directory. Existing destinations are refused. -/
def writeFile (output : System.FilePath) (source : String) : IO Unit := do
  try
    IO.FS.createDir output
  catch
    | .alreadyExists .. => throw (IO.userError s!"output already exists: {output}")
    | error => throw error
  IO.FS.writeFile (output / "Query.lean") source

end Smt2Lean.Emit
