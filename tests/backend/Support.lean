import Smt2Lean.Pipeline
import Lean.Elab.Frontend

open Lean Meta Qq Classical
open Smt2Lean.Backend Smt2Lean.Translate Smt2Lean.Emit

namespace Smt2Lean.Tests

def checkEqual (actual expected : Expr) : MetaM Unit := do
  unless ← isDefEq actual expected do
    throwError "expected {expected}, got {actual}"

def runQuery (env : Environment) (name input : String)
    (check : ParsedQuery → MetaM Unit) : IO Unit :=
  (parseAndInspectQuery input (name := name) fun query => do
    discard <| (check query).toIO { fileName := name, fileMap := default } { env }
  ).runIO

def checkEmission (value : Expr) (kind : GoalKind := .refutation)
    (origin : Option Smt2Lean.Source.Ref := none)
    (assertions : Array Smt2Lean.Source.Ref := #[])
    (parts : Array Smt2Lean.StatementPart := #[]) : MetaM Unit := do
  let (definitionName, theoremName) := match kind with
    | .refutation => (`Refutation, `refutation)
    | .problem => (`Problem, `problem)
  let expectedAxioms ← collectAxioms definitionName
  let source ← render value kind origin assertions (parts := parts)
  for ref in assertions do
    unless ref.names.isEmpty || source.contains ref.namedContext do
      throwError "generated output lost assertion labels"
  let [statements, proofs] := source.splitOn "-- Proofs\n"
    | throwError "expected one Statements section followed by Proofs"
  unless (["Init", "Mathlib.Data.Real.Basic", "Mathlib.Algebra.Order.Archimedean.Real.Basic"].any
      fun module => statements.startsWith s!"import {module}\n\nset_option maxRecDepth 4096\n\n-- Statements\n\n") &&
      proofs.contains s!"theorem {theoremName} : {definitionName} := by\n  sorry\n" do
    throwError "wrong statement/proof layout"
  unsafe enableInitializersExecution
  let some env ← Elab.runFrontend source
      (({} : Options).setBool `Elab.async false) "Query.lean" `Query
    | throwError "generated file did not elaborate"
  let some (.defnInfo definition) := env.find? definitionName
    | throwError "generated statement has no {definitionName} definition"
  let values := #[value] ++ parts.map (·.value)
  let helpers := (values.foldl (fun names value => names ++ value.getUsedConstants) #[]).toList.eraseDups.toArray.filter Smt2Lean.Helpers.isHelper
  -- Generated datatype names alone cannot establish preservation of their meaning.
  for group in (← Smt2Lean.Emit.Datatypes.groups values) do
    for name in group do
      let original ← getConstInfoInduct name
      let emitted ← withEnv env (getConstInfoInduct name)
      unless original.all == emitted.all && original.ctors == emitted.ctors &&
          original.numParams == emitted.numParams && original.numIndices == emitted.numIndices &&
          original.levelParams == emitted.levelParams && !emitted.isUnsafe do
        throwError "generated datatype signature changed: {name}"
      checkEqual emitted.type original.type
      for constructor in original.ctors do
        let original ← getConstInfoCtor constructor
        let emitted ← withEnv env (getConstInfoCtor constructor)
        checkEqual emitted.type original.type
  unless (statements.splitOn "def SMT.").length == helpers.size + 1 do
    throwError "helpers must be emitted once each, and only when used"
  for name in helpers do
    let .defnInfo original ← getConstInfo name | throwError "missing original helper"
    let some (.defnInfo emitted) := env.find? name | throwError "missing emitted helper"
    unless original.levelParams == emitted.levelParams do
      throwError "helper universe parameters changed"
    checkEqual emitted.type original.type
    checkEqual emitted.value original.value
  for part in parts do
    let some (.defnInfo emitted) := env.find? part.name
      | throwError "missing emitted component {part.name}"
    checkEqual emitted.type (← inferType part.value)
    let emittedValue ← withEnv env (deltaExpand emitted.value Smt2Lean.Helpers.isHelper)
    checkEqual emittedValue (← deltaExpand part.value Smt2Lean.Helpers.isHelper)
  checkEqual definition.type q(Prop)
  -- Unfold in each environment separately: matching names alone cannot establish meaning.
  let expand := fun name => Smt2Lean.Helpers.isHelper name || parts.any (·.name == name)
  let emitted ← withEnv env (deltaExpand definition.value expand)
  let original ← deltaExpand value expand
  checkEqual emitted original
  let statementAxioms ← withEnv env (collectAxioms definitionName)
  unless statementAxioms.size == expectedAxioms.size &&
      statementAxioms.all expectedAxioms.contains do
    throwError "generated statement changed axiom dependencies: {statementAxioms}"
  let some (.thmInfo proof) := env.find? theoremName
    | throwError "generated file has no {theoremName} theorem"
  unless proof.type == mkConst definitionName do
    throwError "proof template has the wrong target"
  let axioms ← withEnv env (collectAxioms theoremName)
  unless axioms.contains ``sorryAx && axioms.size == statementAxioms.size + 1 &&
      statementAxioms.all axioms.contains do
    throwError "expected an unfinished proof template"

def checkAxioms (name : Name) (usesClassical : Bool)
    (extraAxioms : Array Name := #[]) : CoreM Unit := do
  let expected := (if usesClassical then #[``propext, ``Classical.choice, ``Quot.sound] else #[]) ++ extraAxioms
  let actual ← collectAxioms name
  unless actual.size == expected.size && actual.all expected.contains do
    throwError "unexpected statement axioms: {actual}; expected {expected}"

def checkRefutation (query : ParsedQuery) (expected : Expr)
    (usesClassical : Bool := false) : MetaM Unit := do
  let statement ← refutationStatement query
  let value := statement.value
  checkEqual value expected
  let .defnInfo definition ← getConstInfo `Refutation
    | throwError "expected a definition named Refutation"
  checkEqual definition.type q(Prop)
  checkEqual definition.value value
  checkAxioms `Refutation usesClassical
  checkEmission value (origin := query.source) (assertions := query.assertionSources) (parts := statement.parts)

def checkClauseValues (parameters actual expected : Array Expr) : MetaM Unit := do
  unless actual.size == expected.size do throwError "wrong reconstructed clause count"
  for value in actual, wanted in expected do
    checkEqual value wanted
    let closed ← mkForallFVars parameters value (usedOnly := false)
    if closed.hasFVar || closed.hasMVar || closed.hasLooseBVars then
      throwError "clause did not close over its relation parameters"
    checkWithKernel closed

def runProblem (env : Environment) (name input : String)
    (check : Smt2Lean.Chc.Problem → MetaM Unit) : IO Unit := do
  (Smt2Lean.Chc.parseAndInspectProblem input (name := name) fun problem => do
    discard <| (check problem).toIO { fileName := name, fileMap := default } { env }
  ).runIO

def checkProblem (problem : Smt2Lean.Chc.Problem) (expected : Expr)
    (usesClassical : Bool := false) (extraAxioms : Array Name := #[]) : MetaM Unit := do
  let statement ← problemStatement problem
  let value := statement.value
  if value.hasFVar || value.hasMVar || value.hasLooseBVars then
    throwError "Problem contains unresolved variables"
  checkEqual value expected
  let .defnInfo definition ← getConstInfo `Problem
    | throwError "expected a definition named Problem"
  checkEqual definition.type q(Prop)
  checkEqual definition.value value
  checkAxioms `Problem usesClassical extraAxioms
  checkEmission value (kind := .problem) (origin := problem.source)
    (assertions := problem.clauses.filterMap (·.source)) (parts := statement.parts)

/-- Even nested reconstructions must not reuse the enclosing query's parameters. -/
def checkFunctionIsolation (query : ParsedQuery) : MetaM Unit :=
  withAssertions query fun parameters _ =>
    withAssertions query fun fresh assertions => do
      for previous in parameters, current in fresh do
        if previous == current || assertions.any (·.containsFVar previous.fvarId!) then
          throwError "function reconstructions shared a parameter"

end Smt2Lean.Tests
