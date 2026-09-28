import Smt2Lean.Emit
import Lean.Elab.Frontend

open Lean Meta Qq
open Smt2Lean.Backend Smt2Lean.Translate Smt2Lean.Emit

private def checkEqual (actual expected : Expr) : MetaM Unit := do
  unless ← isDefEq actual expected do
    throwError "expected {expected}, got {actual}"

private def checkConnectives (query : ParsedQuery) : MetaM Unit :=
  withAssertions query fun parameters assertions => do
    let #[t, a, p, q, r, _] := parameters
      | throwError "expected six declaration parameters"
    let t : Q(Prop) := t
    let a : Q(Prop) := a
    let p : Q(Prop) := p
    let q : Q(Prop) := q
    let r : Q(Prop) := r
    let expected : Array Expr := #[
      t, q($t = $a), q(True), q(¬False), q($p ∧ $q ∧ $r),
      q(¬$p ∨ $q ∨ $r), q($p → $q → $r), q(($p = $q) ∧ ($q = $r)), q($a = $p)
    ]
    unless assertions.size == expected.size do
      throwError "wrong assertion count"
    for actual in assertions, wanted in expected do
      checkEqual actual wanted
    -- A second reconstruction must use its own variables, even in this same context.
    withAssertions query fun other values => do
      unless other[0]! != t && values[0]! == other[0]! do
        throwError "reconstructions shared a variable"

private def checkUnmapped (query : ParsedQuery) : MetaM Unit := do
  let error? ← try
    withAssertions { query with declarations := #[] } fun _ _ => pure ()
    pure none
  catch error => pure (some error)
  let some error := error? | throwError "an unmapped SMT name was accepted"
  unless (← error.toMessageData.toString).contains "undeclared term" do
    throw error

private def runQuery (env : Environment) (name input : String)
    (check : ParsedQuery → MetaM Unit) : IO Unit :=
  (parseAndInspectQuery input (name := name) fun query => do
    discard <| (check query).toIO { fileName := name, fileMap := default } { env }
  ).runIO

private def checkEmission (value : Expr) : MetaM Unit := do
  let source ← render value
  unsafe enableInitializersExecution
  let some env ← Elab.runFrontend source
      (({} : Options).setBool `Elab.async false) "Query.lean" `Query
    | throwError "generated file did not elaborate"
  let some (.defnInfo definition) := env.find? `Refutation
    | throwError "generated statement has no Refutation definition"
  checkEqual definition.value value
  unless (← withEnv env (collectAxioms `Refutation)).isEmpty do
    throwError "generated statement depends on axioms"
  unless (← withEnv env (collectAxioms `refutation)).contains ``sorryAx do
    throwError "expected an unfinished proof template"
  IO.FS.withTempDir fun temporary => do
    let output := temporary / "generated"
    writeFile output source
    let lean := (← findSysroot) / "bin" / "lean"
    let result ← IO.Process.output {
      cmd := lean.toString, args := #["Query.lean"], cwd := some output
      env := #[("LEAN_PATH", some output.toString)]
    }
    unless result.exitCode == 0 do
      throwError "generated file failed to compile: {result.stdout}{result.stderr}"
    -- Protect proof work, even when a caller tries to write the same output again.
    let edited := source ++ "\n-- User proof work.\n"
    IO.FS.writeFile (output / "Query.lean") edited
    let refused ← try
      writeFile output source
      pure false
    catch _ => pure true
    unless refused && (← IO.FS.readFile (output / "Query.lean")) == edited do
      throwError "existing proof work was overwritten"

private def checkRefutation (query : ParsedQuery) (expected : Expr) : MetaM Unit := do
  let value ← defineRefutation query
  checkEqual value expected
  let .defnInfo definition ← getConstInfo `Refutation
    | throwError "expected a definition named Refutation"
  checkEqual definition.type q(Prop)
  checkEqual definition.value value
  checkEmission value

def main : IO Unit := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules #[{ module := `Smt2Lean.Translate }] {} (loadExts := true)
  let input ← IO.FS.readFile "tests/translation/bool/connectives.smt2"
  runQuery env "connectives" input fun query => do
    checkConnectives query
    checkUnmapped query
    checkRefutation query q(∀ (t a p q r _unused : Prop),
      (t ∧ t = a ∧ True ∧ ¬False ∧ (p ∧ q ∧ r) ∧ (¬p ∨ q ∨ r) ∧
        (p → q → r) ∧ (p = q ∧ q = r) ∧ a = p) → False)
  let contradiction ← IO.FS.readFile "tests/translation/bool/contradiction.smt2"
  for status in #["", "sat", "unsat", "unknown"] do
    let metadata := if status.isEmpty then "" else s!"(set-info :status {status})\n"
    runQuery env s!"contradiction ({status})" (metadata ++ contradiction) fun query =>
      checkRefutation query q(∀ p : Prop, (p ∧ ¬p) → False)
  runQuery env "single assertion" (contradiction.replace "(assert (not p))" "") fun query =>
    checkRefutation query q(∀ p : Prop, p → False)
  let empty ← IO.FS.readFile "tests/translation/bool/empty.smt2"
  runQuery env "empty" empty fun query =>
    checkRefutation query q(True → False)
  runQuery env "unused declaration"
    (empty.replace "(check-sat)" "(declare-const unused Bool)\n(check-sat)") fun query =>
      checkRefutation query q(∀ _unused : Prop, True → False)
  let integers ← IO.FS.readFile "tests/translation/int/literals.smt2"
  runQuery env "integer literals" integers fun query => do
    checkUnmapped query
    checkRefutation query q(∀ (x : Int) (p : Prop) (y _unused : Int),
      (x = 0 ∧ y = 340282366920938463463374607431768211457 ∧
        -y = -340282366920938463463374607431768211457 ∧
        (p → x = 0) ∧ (x = 0 ∧ (0 : Int) = -0)) → False)
  runQuery env "unused integer"
    "(set-logic QF_LIA)\n(declare-const unused Int)\n(check-sat)" fun query =>
      checkRefutation query q(∀ _unused : Int, True → False)
  runQuery env "closed integer equality"
    "(set-logic QF_LIA)\n(assert (= 1 2))\n(check-sat)" fun query =>
      checkRefutation query q((1 : Int) = 2 → False)
  IO.println "Translation passed: 11 refutations and generated files; existing proof work preserved"
