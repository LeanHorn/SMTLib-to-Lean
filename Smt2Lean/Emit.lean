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

/-- Keep generated components named, or expose CHC clauses directly in the goal. -/
inductive Layout where
  | structured
  | inline
  deriving BEq

/-- Select the proposition and proof template to emit. -/
inductive GoalKind where
  | refutation
  | problem
  | model
  | safety
  deriving BEq

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
  metadata : Json := .null
  queryNumber : Nat := 1

/-- Public proposition name, preserving the single-query naming convention. -/
def goalName (kind : GoalKind) (number : Option Nat := none) : String :=
  let base := match kind with
    | .refutation => "Refutation"
    | .problem => "Problem"
    | .model => "Model"
    | .safety => "Safe"
  base ++ (number.map (fun n => s!"_{n}") |>.getD "")

/-- Stable semantic category for metadata consumers. -/
def targetKind : GoalKind → String
  | .refutation => "refutation"
  | .problem | .model => "model_existence"
  | .safety => "fixedpoint_safety"

private def checkLayout (goal : Goal) (layout : Layout) : MetaM Unit := do
  if layout == .inline && goal.kind != .problem && goal.kind != .safety then
    throwError "inline layout is supported only for CHC Problem and Safe goals"

/-- Expand only the exact generated wrappers. Beta substitution retains source lets
and sharing lets; source definitions and theory helpers are never selected. -/
private def inlineValue (goal : Goal) : MetaM Expr := do
  let wrappers := goal.parts.foldl (fun values part => values.insert part.name part.value)
    ({} : Std.HashMap Name Expr)
  Core.transform goal.value (pre := fun value => do
    if let .const name _ := value.getAppFn then
      if let some body := wrappers[name]? then
        return .visit (body.betaRev value.getAppRevArgs (useZeta := false))
    return .continue)

/-- Optional kernel check for the rendering transformation itself. The translation
check separately relates the structured target to the original reconstruction. -/
private def checkInline (original expanded : Expr) : MetaM Unit := do
  let declaration : Declaration := .thmDecl {
    name := ← mkFreshId
    levelParams := []
    type := ← mkAppM ``Eq #[original, expanded]
    value := ← mkEqRefl original
  }
  discard <| ofExceptKernelException <|
    (← getEnv).addDeclCore 0 (Lean.maxRecDepth.get (← getOptions)).toUSize declaration none

private def goalValue (goal : Goal) (layout : Layout)
    (checkEquivalence : Bool := false) : MetaM Expr := do
  checkLayout goal layout
  let value ← if layout == .inline then inlineValue goal else pure goal.value
  if layout == .inline && checkEquivalence then checkInline goal.value value
  -- lean-smt's Int.abs is not in Lean core; emit its if/then/else definition.
  deltaExpand value (· == ``Int.abs)

private def sourceComment (label : String) (source : Source.Ref) : String :=
  let span := source.span
  -- Quote filenames and names so newlines cannot escape the Lean comment.
  s!"-- Source: {reprStr source.file}:{span.start.line}:{span.start.column}-" ++
  s!"{span.stop.line}:{span.stop.column} ({label}, command {source.number}){source.namedContext}\n"

/-- Lean prints names starting with ? or # as diagnostic placeholders, without
escaping them. Give these SMT binders ordinary names before pretty-printing. -/
private def printableName (name : Name) : Name :=
  let name := name.eraseMacroScopes
  let text := name.toString (escape := false)
  if text.startsWith "?" || text.startsWith "#" || text == "_" then
    Name.mkSimple ("smt_" ++ text)
  else name

private def printExpr (value : Expr) : MetaM String := do
  let value ← Datatypes.showParameters value
  -- Also cover binders inside lets, lambdas, and nested theory expressions that
  -- are printed by Lean directly instead of printProposition below.
  let value ← Core.transform value (post := fun e => return .done <| match e with
    | .forallE n t b i => .forallE (printableName n) t b i
    | .lam n t b i => .lam (printableName n) t b i
    | .letE n t v b d => .letE (printableName n) t v b d
    | _ =>
      -- Equal total widths can have different splits (1 + 32 versus 28 + 5).
      -- Preserve both append widths so elaboration cannot infer the wrong split.
      if e.isAppOfArity ``BitVec.append 4 then e.setAppPPExplicit else e)
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
  let name := printableName name
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
        printForallGroup type #[← printExpr x] (body.instantiate1 x)
  | _ =>
    if value.isAppOfArity ``Exists 2 then
      let predicate := value.appArg!
      if let .lam name type body info := predicate then
        return ← withLocalDecl (← binderName name body) info type fun x => do
          return s!"∃ ({← printExpr x} : {← printExpr type}),\n{← printProposition (body.instantiate1 x)}"
    if value.isAppOfArity ``And 2 then
      return s!"({← printProposition value.appFn!.appArg!}) ∧\n({← printProposition value.appArg!})"
    printExpr value
where
  -- Equal types can share a binder group; dependent types and premises stop it.
  printForallGroup (type : Expr) (names : Array String) (body : Expr) : MetaM String := do
    if let .forallE name nextType nextBody info := body then
      if nextType == type && !(body.isArrow && (← isProp nextType)) then
        return ← withLocalDecl (← binderName name nextBody) info nextType fun x => do
          printForallGroup type (names.push (← printExpr x)) (nextBody.instantiate1 x)
    return s!"∀ ({String.intercalate " " names.toList} : {← printExpr type}),\n{← printProposition body}"

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
    withLocalDecl (← getUnusedUserName (printableName name)) info type fun x =>
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

private def renderGoal (goal : Goal) (number : Option Nat) (layout : Layout)
    (checkEquivalence : Bool) : MetaM (String × String) := do
  let (baseProof, description, proofTarget) := match goal.kind with
    | .refutation => ("refutation",
        "No interpretation satisfies all assertions of the SMT query.", "the query's refutation")
    | .problem => ("problem",
        "There are interpretations of the declared symbols satisfying every Horn clause.",
        "the existence of a satisfying interpretation")
    | .model => ("model",
        "General model existence: all assertions hold. Outside the Flex Horn adapter.",
        "a satisfying interpretation (use ¬Model to prove unsatisfiability)")
    | .safety => ("safe",
        "There is a rule-closed interpretation excluding the queried relation. Z3 query verdict: unsat.",
        "unreachability; change the target to Reachable to prove reachability")
  let suffix := number.map (fun n => s!"_{n}") |>.getD ""
  let definitionName := goalName goal.kind number
  let theoremName := baseProof ++ suffix
  let value ← goalValue goal layout checkEquivalence
  let needsClassical := (value.find? (·.isConstOf ``Classical.propDecidable)).isSome
  let body ← if goal.parts.isEmpty then printExpr value else printProposition value
  let label := match goal.kind with
    | .refutation | .model => "assertion"
    | .problem | .safety => "clause"
  let queryLabel := number.map (fun n => s!"query {n}: ") |>.getD ""
  let provenance := goal.source.map (sourceComment (queryLabel ++ goal.checkCommand)) |>.getD ""
  let provenance := provenance ++ (if !goal.parts.isEmpty then "" else String.join
    (goal.assertions.mapIdx (fun i ref => sourceComment (if i < goal.assertions.size - goal.assumptionCount then s!"{queryLabel}{label} {i + 1}"
        else s!"{queryLabel}assumption {i + 1 - (goal.assertions.size - goal.assumptionCount)}") ref)).toList)
  let provenance := provenance ++ (if layout == .inline then String.join
    (goal.parts.toList.filterMap fun part =>
      part.source.map (sourceComment (queryLabel ++ part.label))) else "")
  let definition := if needsClassical then
    s!"noncomputable def {definitionName} : Prop := by\n  classical\n  exact\n    " ++
      body.replace "\n" "\n    " ++ "\n"
    else s!"def {definitionName} : Prop :=\n  " ++ body.replace "\n" "\n  " ++ "\n"
  let parts := String.join (← (goal.definitions ++
    (if layout == .structured then goal.parts else #[])).toList.mapM renderPart)
  let dual := if goal.kind == .safety then
      s!"\n/-- The queried relation is reachable. Z3 query verdict: sat. -/\ndef Reachable{suffix} : Prop := ¬{definitionName}\n"
    else ""
  let statement := parts ++ provenance ++ s!"/-- {description} -/\n" ++ definition ++ dual
  let proof := s!"-- Unfinished proof: replace sorry to establish {proofTarget}.\n" ++
    s!"theorem {theoremName} : {definitionName} := by\n  sorry\n"
  return (statement, proof)

/-- Emit helpers once, then all statements, then all unfinished proofs.
Single-query files retain their original goal names. -/
def renderSession (goals : Array Goal) (skipped : Array Source.Command := #[])
    (maxRecDepth : Nat := defaultMaxRecDepth) (scope : Option String := none)
    (layout : Layout := .structured) (checkEquivalence : Bool := false) : MetaM String := do
  if goals.isEmpty then throwError "expected at least one translated query"
  for goal in goals do checkLayout goal layout
  let values := goals.flatMap fun goal => #[goal.value] ++ (goal.definitions ++ goal.parts).map (·.value)
  let datatypeGroups ← Datatypes.groups values
  let datatypeDeclarations ← Datatypes.render datatypeGroups printExpr
  let mut helpers : Array Name := #[]
  for value in values do
    for name in value.getUsedConstants.filter Helpers.isHelper do
      unless helpers.contains name do helpers := helpers.push name
  let helperDefinitions := String.join (← (helpers.qsort Name.lt).toList.mapM renderHelper)
  let entries ← goals.mapIdxM fun i goal =>
    renderGoal goal (if goals.size == 1 then none else some (i + 1)) layout checkEquivalence
  let requests := String.join (skipped.toList.map fun command =>
    sourceComment "unexecuted request" command.source ++ s!"-- Not executed: {reprStr command.text}\n")
  let usesReal := (← Datatypes.usesReal datatypeGroups) || values.any fun value => (value.find? (·.isConstOf ``Real)).isSome
  let usesFloor := values.any fun value => (value.find? (·.isConstOf ``Int.floor)).isSome
  let imports := if usesFloor then "import Mathlib.Algebra.Order.Archimedean.Real.Basic"
    else if usesReal then "import Mathlib.Data.Real.Basic" else "import Init"
  let opening := scope.map (fun name => s!"namespace {name}\n\n") |>.getD ""
  let closing := scope.map (fun name => s!"\nend {name}\n") |>.getD ""
  -- Thousands of small definitions otherwise retain costly async elaboration state.
  -- Scope the option to generated statements so user proofs keep their normal settings.
  return imports ++ s!"\n\nset_option maxRecDepth {maxRecDepth}\n\n" ++ opening ++
    "-- Statements\n\nsection\nset_option Elab.async false\n\n" ++
    requests ++ datatypeDeclarations ++ helperDefinitions ++
    String.intercalate "\n" (entries.toList.map Prod.fst) ++ "\nend\n\n-- Proofs\n\n" ++
    String.intercalate "\n" (entries.toList.map Prod.snd) ++ closing

/-- Walk only the interpretation prefix. Carrier nonemptiness premises separate
carrier binders, while clause variables and model laws lie after this prefix. -/
private partial def interpretationNames (value : Expr) (remaining : Nat) : MetaM (Array String) := do
  if remaining == 0 then return #[]
  if value.isAppOfArity ``Exists 2 then
    if let .lam name type body info := value.appArg! then
      return ← withLocalDecl (← binderName name body) info type fun x => do
        return #[← printExpr x] ++ (← interpretationNames (body.instantiate1 x) (remaining - 1))
  if value.isAppOfArity ``And 2 && value.appFn!.appArg!.isAppOfArity ``Nonempty 1 then
    return ← interpretationNames value.appArg! remaining
  throwError "CHC metadata does not match the emitted interpretation binders"

private def qualifiedName (scope : Option String) (name : String) : String :=
  scope.map (fun namespaceName => namespaceName ++ "." ++ name) |>.getD name

/-- Attach final printed names without parsing Lean text or traversing clause binders. -/
private def goalMetadata (goal : Goal) (number : Option Nat) (scope : Option String)
    (layout : Layout) : MetaM Json := do
  checkLayout goal layout
  let symbols := ((goal.metadata.getObjValD "symbols").getArr?).toOption.getD #[]
  let names ← if symbols.isEmpty then pure #[] else
    interpretationNames (← goalValue goal layout) symbols.size
  let symbols ← symbols.mapM fun (symbol : Json) => do
    let index ← Lean.ofExcept ((symbol.getObjValD "parameter_index").getNat?)
    let some name := names[index]?
      | throwError "CHC metadata parameter index {index} is outside the interpretation prefix"
    return symbol.mergeObj (Json.mkObj [("emitted_binder", toJson name)])
  let clauses := ((goal.metadata.getObjValD "clauses").getArr?).toOption.getD #[]
  let clauses := clauses.map fun clause =>
    match (clause.getObjValD "wrapper_name").getStr? with
    | .ok name => clause.mergeObj <|
        Json.mkObj [("wrapper_name", toJson (qualifiedName scope name))]
    | .error _ => clause
  let metadata := goal.metadata.mergeObj <| Json.mkObj [
    ("query_number", toJson goal.queryNumber),
    ("goal_name", toJson (qualifiedName scope (goalName goal.kind number))),
    ("target_kind", toJson (targetKind goal.kind)),
    ("horn", toJson (goal.kind == .problem || goal.kind == .safety)),
    ("layout", toJson (if layout == .structured then "structured" else "inline")),
    ("wrappers_emitted", toJson (layout == .structured)),
    ("wrapper_names", toJson (goal.parts.map fun part => qualifiedName scope part.name.toString)),
    ("symbols", toJson symbols)]
  return if clauses.isEmpty then metadata else
    metadata.mergeObj (Json.mkObj [("clauses", toJson clauses)])

/-- Query metadata uses exactly the declaration names and binders rendered above. -/
def renderMetadata (goals : Array Goal) (scope : Option String := none)
    (layout : Layout := .structured) : MetaM (Array Json) :=
  goals.mapIdxM fun i goal =>
    goalMetadata goal (if goals.size == 1 then none else some (i + 1)) scope layout

/-- Render one file with statements first, followed by unfinished proofs. -/
def render (value : Expr) (kind : GoalKind := .refutation)
    (source : Option Source.Ref := none) (assertions : Array Source.Ref := #[])
    (maxRecDepth : Nat := defaultMaxRecDepth) (parts : Array StatementPart := #[])
    (definitions : Array StatementPart := #[]) (layout : Layout := .structured)
    (checkEquivalence : Bool := false) : MetaM String :=
  renderSession #[{ value, parts, definitions, kind, source, assertions }]
    (maxRecDepth := maxRecDepth) (layout := layout) (checkEquivalence := checkEquivalence)

/-- Write Query.lean in a new directory. Existing destinations are refused. -/
def writeFile (output : System.FilePath) (source : String) : IO Unit := do
  try
    IO.FS.createDir output
  catch
    | .alreadyExists .. => throw (IO.userError s!"output already exists: {output}")
    | error => throw error
  IO.FS.writeFile (output / "Query.lean") source

end Smt2Lean.Emit
