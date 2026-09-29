import Smt2Lean.Emit
import Lean.Elab.Frontend

open Lean Meta Qq Classical
open Smt2Lean.Backend Smt2Lean.Translate Smt2Lean.Emit

local notation "exclusive" => (fun p q : Prop => (p ∧ ¬q) ∨ (¬p ∧ q))

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
      q(¬$p ∨ $q ∨ $r), q($p → $q → $r), q(($p = $q) ∧ ($q = $r)), q($a = $p),
      q(exclusive $p (¬$q)), q(exclusive (exclusive $p $q) $r),
      q(¬exclusive (exclusive (exclusive $p $q) $r) True),
      q($p ≠ False), q(¬($p ≠ $q ∧ $p ≠ $r ∧ $q ≠ $r)),
      q(if $p then $q else $r), q(if (if $p then $q else $r) then ¬False else False),
      q(if $p = $q then $p else ¬$p)
    ]
    unless assertions.size == expected.size do
      throwError "wrong assertion count"
    for actual in assertions, wanted in expected do
      checkEqual actual wanted
    unless assertions[9]!.isAppOf `SMT.xor &&
        assertions[12]!.isAppOf `SMT.distinct2 &&
        assertions[13]!.appArg!.isAppOf `SMT.distinct3 do
      throwError "xor/distinct were expanded instead of calling their helpers"
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
  let message ← error.toMessageData.toString
  unless message.contains "undeclared term" do
    throw error
  let some source := query.assertionSources[0]? | throwError "missing assertion source"
  unless message.contains s!"{source.context}: assertion 1:" do
    throwError "reconstruction error lost its source: {message}"

/-- Even nested reconstructions must not reuse the enclosing query's parameters. -/
private def checkFunctionIsolation (query : ParsedQuery) : MetaM Unit :=
  withAssertions query fun parameters _ =>
    withAssertions query fun fresh assertions => do
      for previous in parameters, current in fresh do
        if previous == current || assertions.any (·.containsFVar previous.fvarId!) then
          throwError "function reconstructions shared a parameter"

private def runQuery (env : Environment) (name input : String)
    (check : ParsedQuery → MetaM Unit) : IO Unit :=
  (parseAndInspectQuery input (name := name) fun query => do
    discard <| (check query).toIO { fileName := name, fileMap := default } { env }
  ).runIO

private def checkEmission (value : Expr) (kind : GoalKind := .refutation)
    (origin : Option Smt2Lean.Source.Ref := none)
    (assertions : Array Smt2Lean.Source.Ref := #[]) : MetaM Unit := do
  let (definitionName, theoremName) := match kind with
    | .refutation => (`Refutation, `refutation)
    | .problem => (`Problem, `problem)
  let expectedAxioms ← collectAxioms definitionName
  let source ← render value kind origin assertions
  let [statements, proofs] := source.splitOn "-- Proofs\n"
    | throwError "expected one Statements section followed by Proofs"
  unless statements.startsWith "import Init\n\n-- Statements\n\n" &&
      proofs.contains s!"theorem {theoremName} : {definitionName} := by\n  sorry\n" do
    throwError "wrong statement/proof layout"
  unsafe enableInitializersExecution
  let some env ← Elab.runFrontend source
      (({} : Options).setBool `Elab.async false) "Query.lean" `Query
    | throwError "generated file did not elaborate"
  let some (.defnInfo definition) := env.find? definitionName
    | throwError "generated statement has no {definitionName} definition"
  let helpers := value.getUsedConstants.filter Smt2Lean.Helpers.isHelper
  unless (statements.splitOn "def SMT.").length == helpers.size + 1 do
    throwError "helpers must be emitted once each, and only when used"
  for name in helpers do
    let .defnInfo original ← getConstInfo name | throwError "missing original helper"
    let some (.defnInfo emitted) := env.find? name | throwError "missing emitted helper"
    unless original.levelParams == emitted.levelParams do
      throwError "helper universe parameters changed"
    checkEqual emitted.type original.type
    checkEqual emitted.value original.value
  checkEqual definition.type q(Prop)
  -- Unfold in each environment separately: matching names alone cannot establish meaning.
  let emitted ← withEnv env (deltaExpand definition.value Smt2Lean.Helpers.isHelper)
  let original ← deltaExpand value Smt2Lean.Helpers.isHelper
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
  IO.FS.withTempDir fun temporary => do
    let output := temporary / "generated"
    writeFile output source
    let #[entry] ← output.readDir
      | throwError "expected exactly one generated Query.lean"
    unless entry.fileName == "Query.lean" do
      throwError "expected exactly one generated Query.lean"
    -- Check the statement independently, without the admitted theorem.
    IO.FS.writeFile (temporary / "StatementsOnly.lean") statements
    let lean := (← findSysroot) / "bin" / "lean"
    for (directory, file) in #[(output, "Query.lean"), (temporary, "StatementsOnly.lean")] do
      let result ← IO.Process.output {
        cmd := lean.toString, args := #[file], cwd := some directory
        env := #[("LEAN_PATH", some directory.toString)]
      }
      unless result.exitCode == 0 do
        throwError "{file} failed to compile: {result.stdout}{result.stderr}"
    -- Protect proof work, even when a caller tries to write the same output again.
    let edited := source ++ "\n-- User proof work.\n"
    IO.FS.writeFile (output / "Query.lean") edited
    let refused ← try
      writeFile output source
      pure false
    catch _ => pure true
    unless refused && (← IO.FS.readFile (output / "Query.lean")) == edited do
      throwError "existing proof work was overwritten"

private def checkAxioms (name : Name) (usesClassical : Bool) : CoreM Unit := do
  let expected := if usesClassical then #[``propext, ``Classical.choice, ``Quot.sound] else #[]
  let actual ← collectAxioms name
  unless actual.size == expected.size && actual.all expected.contains do
    throwError "unexpected statement axioms: {actual}; expected {expected}"

private def checkRefutation (query : ParsedQuery) (expected : Expr)
    (usesClassical : Bool := false) : MetaM Unit := do
  let value ← defineRefutation query
  checkEqual value expected
  let .defnInfo definition ← getConstInfo `Refutation
    | throwError "expected a definition named Refutation"
  checkEqual definition.type q(Prop)
  checkEqual definition.value value
  checkAxioms `Refutation usesClassical
  checkEmission value (origin := query.source) (assertions := query.assertionSources)

private def checkClauseValues (parameters actual expected : Array Expr) : MetaM Unit := do
  unless actual.size == expected.size do throwError "wrong reconstructed clause count"
  for value in actual, wanted in expected do
    checkEqual value wanted
    let closed ← mkForallFVars parameters value (usedOnly := false)
    if closed.hasFVar || closed.hasMVar || closed.hasLooseBVars then
      throwError "clause did not close over its relation parameters"
    checkWithKernel closed

/-- Check xor against odd parity, independently of its chosen Lean encoding. -/
private def checkOperatorSemantics (env : Environment) : IO Unit := do
  let mut cases : Array (String × Bool) := #[]
  for arity in [2:5] do
    for mask in [:2 ^ arity] do
      let bits := (List.range arity).map (fun i => mask.testBit i)
      let operands := String.intercalate " " (bits.map fun b => if b then "true" else "false")
      cases := cases.push (s!"(xor {operands})", bits.count true % 2 == 1)
  cases := cases ++ #[("(distinct 1 2)", true), ("(distinct 1 2 3 4)", true),
    ("(distinct 1 2 1)", false), ("(distinct 1 2 3 1)", false)]
  for condition in [false, true] do
    for yes in [false, true] do
      for no in [false, true] do
        cases := cases.push (s!"(ite {condition} {yes} {no})", if condition then yes else no)
  cases := cases ++ #[
    ("(= (ite true (- 7) 19) (- 7))", true),
    ("(= (ite false (- 7) 19) (- 7))", false),
    ("(= (ite false 0 340282366920938463463374607431768211457) 340282366920938463463374607431768211457)", true),
    ("(= (ite true (ite false 3 5) 7) 5)", true)]
  let input := "(set-logic ALL)\n" ++
    String.join (cases.toList.map fun (term, _) => s!"(assert {term})\n") ++ "(check-sat)"
  runQuery env "operator truth cases" input fun query => do
    withAssertions query fun parameters assertions => do
      unless parameters.isEmpty && assertions.size == cases.size do
        throwError "wrong truth-case count or unexpected parameters"
      for actual in assertions, (term, expected) in cases do
        let actual : Q(Prop) := actual
        let target := if expected then actual else q(¬$actual)
        let proof ← mkDecideProof (← deltaExpand target Smt2Lean.Helpers.isHelper)
        checkEqual (← inferType proof) target
        try checkWithKernel proof
        catch _ => throwError "wrong truth value for {term}: expected {expected}"
    let value ← defineRefutation query
    checkAxioms `Refutation false
    checkEmission value (origin := query.source)
      (assertions := query.assertionSources)
  runQuery env "quantified operators"
    "(set-logic ALL)\n(declare-fun f (Bool) Int)\n\
     (assert (forall ((b Bool) (c Bool) (x Int) (y Int))\
       (=> (xor b c) (distinct (f (xor b c)) x y))))\n(check-sat)" fun query =>
      checkRefutation query q(∀ f : Prop → Int,
        (∀ (b c : Prop) (x y : Int), exclusive b c →
          (f (exclusive b c) ≠ x ∧ f (exclusive b c) ≠ y ∧ x ≠ y)) → False)
  IO.println "Operator semantics passed: 28 xor, 4 distinct, 8 Bool ite, 4 Int ite cases, and quantified arguments"

/-- Allow classical decidability without admitting unfinished or invented statements. -/
private def checkAxiomRejection : IO Unit := do
  unsafe enableInitializersExecution
  let some env ← Elab.runFrontend
      "import Init\naxiom fabricated : Prop\ndef hidden : Prop := fabricated\n\
       def admitted : Prop := by sorry\ndef hiddenAdmission : Prop := admitted\n\
       noncomputable def conditional : Prop := by\n  classical\n\
         exact ∀ p : Prop, (if p then (1 : Int) else 0) = 1\n"
      (({} : Options).setBool `Elab.async false) "AxiomRejection.lean" `AxiomRejection
    | throw (IO.userError "could not build axiom rejection cases")
  let check : CoreM Unit := do
    checkStatementAxioms `conditional
    checkAxioms `conditional true
    for (name, reason) in #[(`hidden, "fabricated"), (`hiddenAdmission, "sorryAx")] do
      let error? ← try
        checkStatementAxioms name
        pure none
      catch error => pure (some error)
      let some error := error? | throwError "accepted forbidden axioms in {name}"
      unless (← error.toMessageData.toString).contains reason do throw error
  discard <| check.toIO { fileName := "axiom checks", fileMap := default } { env }
  IO.println "Axiom checks passed: only Lean foundations allowed; transitive admissions rejected"

private def runProblem (env : Environment) (name input : String)
    (check : Smt2Lean.Chc.Problem → MetaM Unit) : IO Unit := do
  (Smt2Lean.Chc.parseAndInspectProblem input (name := name) fun problem => do
    discard <| (check problem).toIO { fileName := name, fileMap := default } { env }
  ).runIO

private def checkHornReconstruction (env : Environment) : IO Unit := do
  let path := "tests/chc/lh_sum_rec.smt2"
  runProblem env path (← IO.FS.readFile path) fun problem =>
    withClauses problem fun parameters clauses => do
      let #[k] := parameters | throwError "expected one relation parameter"
      let k : Q(Int → Prop) := k
      checkClauseValues parameters clauses #[
        q(∀ (n : Int) (cond : Prop) (vv : Int),
          (cond = (n ≤ 0)) → cond → vv = 0 → $k vv),
        q(∀ (n : Int) (cond : Prop) (n1 t1 v : Int),
          (cond = (n ≤ 0)) → ¬cond → n1 = n - 1 → $k t1 → v = n + t1 → $k v),
        q(∀ (r : Int) (ok1 v : Prop),
          $k r → (ok1 = (0 ≤ r)) → (v = (0 ≤ r)) → v = ok1 → ¬v → False)
      ]
  let path := "tests/translation/chc/clauses.smt2"
  runProblem env path (← IO.FS.readFile path) fun problem => do
    withClauses problem fun parameters clauses => do
      let #[p, r, done, namedTrue, quoted, unused] := parameters
        | throwError "expected six relation parameters"
      let p : Q(Int → Prop) := p
      let r : Q(Int → Prop → Int → Prop) := r
      let done : Q(Prop) := done
      let namedTrue : Q(Prop) := namedTrue
      let quoted : Q(Prop → Int → Prop) := quoted
      checkEqual (← inferType unused) q(Int → Prop → Prop)
      checkClauseValues parameters clauses #[
        q($p 0), q($r 7 (True ∧ ¬False) (9 - 4)), done, namedTrue,
        q($quoted ((1 : Int) = 2) (10 + 2)),
        q(∀ (x : Int) (_p : Prop) (_unused : Int), $p x),
        q(∀ (x y : Int) (b : Prop), $p x → y > x → b → $r (x + 1) b x),
        q(∀ x : Int, x > 0 → $p x → $done),
        q(∀ (outer inner : Int) (flag : Prop) (onlyBody : Int) (_unused : Prop),
          outer < inner → flag → onlyBody = 7 → $r outer flag inner),
        q($done → False), q(False),
        q(∀ (x y : Int) (cond : Prop), $p x → x > 0 → $p y →
          ((x < 0 ∧ y > 0) ∨ ¬cond) → $done →
          (cond = (x * y + -x > Int.abs y)) → ¬cond → False),
        q(∀ (x y : Int) (b c : Prop), $p x → exclusive b c →
          (x ≠ y ∧ x ≠ 0 ∧ y ≠ 0) → b ≠ c → $r x (exclusive b (x ≠ y)) y),
        q(∀ (x y : Int) (b c : Prop), $p x → (if b then x < y else x = y) →
          $r (if b then x else y) (if c then b else x < y) (if x < y then x + 1 else y))
      ]
      -- Nested calls must allocate their own relations and clause variables.
      withClauses problem fun fresh values => do
        for previous in parameters, current in fresh do
          if previous == current || values.any (·.containsFVar previous.fvarId!) then
            throwError "CHC reconstructions shared a relation parameter"
    -- A missing relation named True must not fall back to Lean's builtin True.
    let some fact := problem.clauses[3]? | throwError "missing True fact"
    let error? ← try
      withClauses { problem with relations := #[], clauses := #[fact] } fun _ _ => pure ()
      pure none
    catch error => pure (some error)
    let some error := error? | throwError "accepted an unmapped relation named True"
    let message ← error.toMessageData.toString
    unless message.contains "unmapped CHC relation: True" do
      throw error
    let some source := fact.source | throwError "missing clause source"
    unless message.contains s!"{source.context true}: clause 4:" do
      throwError "CHC reconstruction error lost its source: {message}"
  IO.println "CHC reconstruction passed: 17 clauses match handwritten Lean propositions"

private def checkProblem (problem : Smt2Lean.Chc.Problem) (expected : Expr)
    (usesClassical : Bool := false) : MetaM Unit := do
  let value ← defineProblem problem
  if value.hasFVar || value.hasMVar || value.hasLooseBVars then
    throwError "Problem contains unresolved variables"
  checkEqual value expected
  let .defnInfo definition ← getConstInfo `Problem
    | throwError "expected a definition named Problem"
  checkEqual definition.type q(Prop)
  checkEqual definition.value value
  checkAxioms `Problem usesClassical
  checkEmission value (kind := .problem) (origin := problem.source)
    (assertions := problem.clauses.filterMap (·.source))

private def checkHornProblems (env : Environment) : IO Unit := do
  let path := "tests/chc/lh_sum_rec.smt2"
  let input ← IO.FS.readFile path
  let expected := q(∃ k : Int → Prop,
    (∀ (n : Int) (cond : Prop) (vv : Int),
      (cond = (n ≤ 0)) → cond → vv = 0 → k vv) ∧
    (∀ (n : Int) (cond : Prop) (n1 t1 v : Int),
      (cond = (n ≤ 0)) → ¬cond → n1 = n - 1 → k t1 → v = n + t1 → k v) ∧
    (∀ (r : Int) (ok1 v : Prop),
      k r → (ok1 = (0 ≤ r)) → (v = (0 ≤ r)) → v = ok1 → ¬v → False))
  for status in #["", "sat", "unsat", "unknown"] do
    let metadata := if status.isEmpty then "" else s!"(set-info :status {status})"
    runProblem env s!"{path} ({status})" (input.replace "(set-info :status sat)" metadata)
      fun problem => checkProblem problem expected
  let path := "tests/translation/chc/clauses.smt2"
  runProblem env path (← IO.FS.readFile path) fun problem =>
    checkProblem problem (usesClassical := true) q(∃ (p : Int → Prop) (r : Int → Prop → Int → Prop)
      (done namedTrue : Prop) (quoted : Prop → Int → Prop) (_unused : Int → Prop → Prop),
      p 0 ∧ r 7 (True ∧ ¬False) (9 - 4) ∧ done ∧ namedTrue ∧
      quoted ((1 : Int) = 2) (10 + 2) ∧
      (∀ (x : Int) (_p : Prop) (_unused : Int), p x) ∧
      (∀ (x y : Int) (b : Prop), p x → y > x → b → r (x + 1) b x) ∧
      (∀ x : Int, x > 0 → p x → done) ∧
      (∀ (outer inner : Int) (flag : Prop) (onlyBody : Int) (_unused : Prop),
        outer < inner → flag → onlyBody = 7 → r outer flag inner) ∧
      (done → False) ∧ False ∧
      (∀ (x y : Int) (cond : Prop), p x → x > 0 → p y →
        ((x < 0 ∧ y > 0) ∨ ¬cond) → done →
        (cond = (x * y + -x > Int.abs y)) → ¬cond → False) ∧
      (∀ (x y : Int) (b c : Prop), p x → exclusive b c →
        (x ≠ y ∧ x ≠ 0 ∧ y ≠ 0) → b ≠ c → r x (exclusive b (x ≠ y)) y) ∧
      (∀ (x y : Int) (b c : Prop), p x → (if b then x < y else x = y) →
        r (if b then x else y) (if c then b else x < y) (if x < y then x + 1 else y)))
  let cases : Array (String × String × Expr) := #[
    ("empty", "", q(True)),
    ("unused relations", "(declare-const p Bool)\n(declare-fun R (Int Bool) Bool)",
      q(∃ (_p : Prop) (_r : Int → Prop → Prop), True)),
    ("nullary fact", "(declare-const p Bool)\n(assert p)", q(∃ p : Prop, p)),
    ("bare false", "(assert false)", q(False)),
    ("nullary contradiction", "(declare-const p Bool)\n(assert p)\n(assert (=> p false))",
      q(∃ p : Prop, p ∧ (p → False)))
  ]
  for (name, body, expected) in cases do
    runProblem env name ("(set-logic HORN)\n" ++ body ++ "\n(check-sat)")
      fun problem => checkProblem problem expected
  IO.println "CHC problems passed: 10 complete propositions and standalone files; axiom dependencies checked"

def main : IO Unit := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules #[{ module := `Smt2Lean.Translate }] {} (loadExts := true)
  checkAxiomRejection
  checkOperatorSemantics env
  checkHornReconstruction env
  checkHornProblems env
  let input ← IO.FS.readFile "tests/translation/bool/connectives.smt2"
  runQuery env "connectives" input fun query => do
    checkConnectives query
    checkUnmapped query
    checkRefutation query (usesClassical := true) q(∀ (t a p q r _unused : Prop),
      (t ∧ t = a ∧ True ∧ ¬False ∧ (p ∧ q ∧ r) ∧ (¬p ∨ q ∨ r) ∧
        (p → q → r) ∧ (p = q ∧ q = r) ∧ a = p ∧
        exclusive p (¬q) ∧ exclusive (exclusive p q) r ∧
        ¬exclusive (exclusive (exclusive p q) r) True ∧
        p ≠ False ∧ ¬(p ≠ q ∧ p ≠ r ∧ q ≠ r) ∧
        (if p then q else r) ∧ (if (if p then q else r) then ¬False else False) ∧
        (if p = q then p else ¬p)) → False)
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
  let arithmetic ← IO.FS.readFile "tests/translation/int/arithmetic.smt2"
  runQuery env "integer arithmetic" arithmetic fun query =>
    checkRefutation query (usesClassical := true) q(
      let abs := fun x : Int => if x < 0 then -x else x
      ∀ (x y z : Int) (p : Prop),
        ((x + y + z + 7) = (x - y - z) ∧ (x * y * z) = (x * -y) ∧ -(-x) = x ∧
          (p → abs (-x) = abs x) ∧ abs (abs x) = abs x ∧
          ((7 : Int) = 7 ∧ (0 : Int) = 0 ∧ (9 : Int) = 9) ∧
          (340282366920938463463374607431768211457 : Int) + -1 =
            340282366920938463463374607431768211456 ∧
          (10 : Int) - 3 - 2 = 5 ∧
          x ≠ y ∧ (x ≠ y ∧ x ≠ z ∧ x ≠ 7 ∧ y ≠ z ∧ y ≠ 7 ∧ z ≠ 7) ∧
          ¬(x ≠ y ∧ x ≠ x ∧ y ≠ x) ∧
          (if p then x else y) + 1 = (if x < y then x + 1 else y - 1) ∧
          (if p then (if x > y then x else y) else z) =
            (if ¬p then z else (if x > y then x else y)) ∧
          (if x < y then x else y) = (if True then (if False then y else x) else y) ∧
          (p → (x < y ∧ y < z ∧ z < x + 1) ∧
               (x ≤ y ∧ y ≤ z ∧ z ≤ x + 2) ∧
               (x > y ∧ y > z ∧ z > x - 1) ∧
               (x ≥ y ∧ y ≥ z ∧ z ≥ x - 2))) → False)
  let bounds ← IO.FS.readFile "tests/translation/int/bounds.smt2"
  runQuery env "integer bounds" bounds fun query =>
    checkRefutation query q(∀ x : Int, (x ≥ 0 ∧ x < 0) → False)
  let functions ← IO.FS.readFile "tests/translation/functions/applications.smt2"
  runQuery env "functions and predicates" functions fun query => do
    checkUnmapped query
    checkFunctionIsolation query
    checkRefutation query (usesClassical := true) q(∀ (f : Int → Int) (g namedAdd : Int → Int → Int)
      (_unused : Int → Int) (x y : Int) (p : Prop) (P : Int → Prop) (R : Int → Int → Prop)
      (b : Prop → Prop) (choose : Prop → Int → Int) (test : Int → Prop → Prop)
      (namedTrue : Prop → Int) (_unusedBool : Prop → Int → Prop),
      (g x y = f x - f y ∧ f (g y x) = g (f y) (f x) ∧ namedAdd x y = x - y ∧
        (p → f (x + 1) > f x) ∧ g x x = f (f x) ∧
        f 340282366920938463463374607431768211457 = g 0 (-1) ∧
        (P x ∧ ¬P (f x)) ∧ (P (g x y) → R (f x) (g y x)) ∧ R x y = p ∧
        choose p (f x) = choose (¬p) y ∧ test x (p ∧ P x) ∧ b (¬p) = (P y ∨ R x y) ∧
        b (b True) = b False ∧ choose (x = y) (x - y) = namedTrue (p → P (f x)) ∧
        test (choose (P (f x)) (g x y)) (b p) = b (p = P x) ∧
        choose (if p then P x else ¬P y) (if P x then f y else x) = f (if p then x else y)) → False)
  -- Reuse f and x in separate inputs with different signatures and scalar sorts.
  runQuery env "Bool to Int"
    "(set-logic ALL)\n(declare-fun f (Bool) Int)\n(declare-const x Bool)\n(assert (= (f x) 1))\n(check-sat)"
    fun query => checkRefutation query q(∀ (f : Prop → Int) (x : Prop), f x = 1 → False)
  runQuery env "Int to Bool"
    "(set-logic ALL)\n(declare-fun f (Int) Bool)\n(declare-const x Int)\n(assert (f x))\n(check-sat)"
    fun query => checkRefutation query q(∀ (f : Int → Prop) (x : Int), f x → False)
  let congruence ← IO.FS.readFile "tests/translation/functions/congruence.smt2"
  runQuery env "function congruence" congruence fun query =>
    checkRefutation query q(∀ (f : Int → Int) (x y : Int), (x = y ∧ ¬f x = f y) → False)
  let scopes ← IO.FS.readFile "tests/translation/quantifiers/scopes.smt2"
  runQuery env "quantifier scopes" scopes fun query => do
    checkUnmapped query
    checkFunctionIsolation query
    checkRefutation query (usesClassical := true) q(∀ (x : Int) (p : Prop) (R : Int → Int → Prop → Prop)
      (f : Prop → Int → Int) (namedTrue : Prop → Prop),
      ((∀ (a : Int) (b : Prop), ∃ y : Int, y = a + 1 ∧ R a y b) ∧
       (∃ a : Int, ∀ y : Int, R a y p) ∧
       (x = 7 ∧ (∀ a : Int, a ≥ 0 ∧ (∃ b : Int, b < 0) ∧ a = 1) ∧ x = 8) ∧
       (∀ a : Int, (∃ b : Int, R a b p) ∧ (∃ b : Prop, R a 0 b) ∧ R a a p) ∧
       ((∀ (t : Prop) (a : Int), ∃ b : Prop, R a (f (t ∧ b) x) (¬t)) ∧ namedTrue p) ∧
       ((∀ (b : Prop) (y : Int), (b ∧ y = x) → R x x p) ∧
         (∀ (_unused : Int) (_flag : Prop), p) ∧ (∃ _unused : Prop, ∃ _value : Int, p)) ∧
       f (∃ y : Int, y = x) x = f (∀ y : Int, R x y p) 0 ∧
       ((∀ z : Int, R z x p) ∧ (∃ z : Int, R z x p)) ∧
       (∀ (b : Prop) (a : Int),
         (if (∃ z : Int, R z z b) then (if b then a else 0)
          else (if (∀ c : Prop, c) then 1 else a)) = a)) → False)
  let quantified ← IO.FS.readFile "tests/translation/quantifiers/quantified.smt2"
  for status in #["", "sat", "unsat", "unknown"] do
    let metadata := if status.isEmpty then "" else s!"(set-info :status {status})\n"
    runQuery env s!"quantified ({status})" (metadata ++ quantified) fun query =>
      checkRefutation query q(∀ P : Int → Prop, ((∀ x : Int, P x) ∧ (∃ x : Int, ¬P x)) → False)
  IO.println "Translation passed: 24 refutations and generated files; existing proof work preserved"
