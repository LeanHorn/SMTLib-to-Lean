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

private def checkEmission (value : Expr) (kind : GoalKind := .refutation) : MetaM Unit := do
  let (definitionName, theoremName) := match kind with
    | .refutation => (`Refutation, `refutation)
    | .problem => (`Problem, `problem)
  let source ← render value kind
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
  checkEqual definition.type q(Prop)
  checkEqual definition.value value
  unless (← withEnv env (collectAxioms definitionName)).isEmpty do
    throwError "generated statement depends on axioms"
  let some (.thmInfo proof) := env.find? theoremName
    | throwError "generated file has no {theoremName} theorem"
  unless proof.type == mkConst definitionName do
    throwError "proof template has the wrong target"
  let axioms ← withEnv env (collectAxioms theoremName)
  unless axioms.size == 1 && axioms.contains ``sorryAx do
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

private def checkRefutation (query : ParsedQuery) (expected : Expr) : MetaM Unit := do
  let value ← defineRefutation query
  checkEqual value expected
  let .defnInfo definition ← getConstInfo `Refutation
    | throwError "expected a definition named Refutation"
  checkEqual definition.type q(Prop)
  checkEqual definition.value value
  checkEmission value

private def checkClauseValues (parameters actual expected : Array Expr) : MetaM Unit := do
  unless actual.size == expected.size do throwError "wrong reconstructed clause count"
  for value in actual, wanted in expected do
    checkEqual value wanted
    let closed ← mkForallFVars parameters value (usedOnly := false)
    if closed.hasFVar || closed.hasMVar || closed.hasLooseBVars then
      throwError "clause did not close over its relation parameters"
    checkWithKernel closed

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
          (cond = (x * y + -x > Int.abs y)) → ¬cond → False)
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
    unless (← error.toMessageData.toString).contains "unmapped CHC relation: True" do
      throw error
  IO.println "CHC reconstruction passed: 15 clauses match handwritten Lean propositions"

private def checkProblem (problem : Smt2Lean.Chc.Problem) (expected : Expr) : MetaM Unit := do
  let value ← defineProblem problem
  if value.hasFVar || value.hasMVar || value.hasLooseBVars then
    throwError "Problem contains unresolved variables"
  checkEqual value expected
  let .defnInfo definition ← getConstInfo `Problem
    | throwError "expected a definition named Problem"
  checkEqual definition.type q(Prop)
  checkEqual definition.value value
  unless (← collectAxioms `Problem).isEmpty do
    throwError "Problem depends on axioms"
  checkEmission value (kind := .problem)

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
    checkProblem problem q(∃ (p : Int → Prop) (r : Int → Prop → Int → Prop)
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
        (cond = (x * y + -x > Int.abs y)) → ¬cond → False))
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
  IO.println "CHC problems passed: 10 complete propositions and standalone files; statements axiom-free, proofs admitted"

def main : IO Unit := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules #[{ module := `Smt2Lean.Translate }] {} (loadExts := true)
  checkHornReconstruction env
  checkHornProblems env
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
  let arithmetic ← IO.FS.readFile "tests/translation/int/arithmetic.smt2"
  runQuery env "integer arithmetic" arithmetic fun query =>
    checkRefutation query q(
      let abs := fun x : Int => if x < 0 then -x else x
      ∀ (x y z : Int) (p : Prop),
        ((x + y + z + 7) = (x - y - z) ∧ (x * y * z) = (x * -y) ∧ -(-x) = x ∧
          (p → abs (-x) = abs x) ∧ abs (abs x) = abs x ∧
          ((7 : Int) = 7 ∧ (0 : Int) = 0 ∧ (9 : Int) = 9) ∧
          (340282366920938463463374607431768211457 : Int) + -1 =
            340282366920938463463374607431768211456 ∧
          (10 : Int) - 3 - 2 = 5 ∧
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
    checkRefutation query q(∀ (f : Int → Int) (g namedAdd : Int → Int → Int)
      (_unused : Int → Int) (x y : Int) (p : Prop) (P : Int → Prop) (R : Int → Int → Prop)
      (b : Prop → Prop) (choose : Prop → Int → Int) (test : Int → Prop → Prop)
      (namedTrue : Prop → Int) (_unusedBool : Prop → Int → Prop),
      (g x y = f x - f y ∧ f (g y x) = g (f y) (f x) ∧ namedAdd x y = x - y ∧
        (p → f (x + 1) > f x) ∧ g x x = f (f x) ∧
        f 340282366920938463463374607431768211457 = g 0 (-1) ∧
        (P x ∧ ¬P (f x)) ∧ (P (g x y) → R (f x) (g y x)) ∧ R x y = p ∧
        choose p (f x) = choose (¬p) y ∧ test x (p ∧ P x) ∧ b (¬p) = (P y ∨ R x y) ∧
        b (b True) = b False ∧ choose (x = y) (x - y) = namedTrue (p → P (f x)) ∧
        test (choose (P (f x)) (g x y)) (b p) = b (p = P x)) → False)
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
    checkRefutation query q(∀ (x : Int) (p : Prop) (R : Int → Int → Prop → Prop)
      (f : Prop → Int → Int) (namedTrue : Prop → Prop),
      ((∀ (a : Int) (b : Prop), ∃ y : Int, y = a + 1 ∧ R a y b) ∧
       (∃ a : Int, ∀ y : Int, R a y p) ∧
       (x = 7 ∧ (∀ a : Int, a ≥ 0 ∧ (∃ b : Int, b < 0) ∧ a = 1) ∧ x = 8) ∧
       (∀ a : Int, (∃ b : Int, R a b p) ∧ (∃ b : Prop, R a 0 b) ∧ R a a p) ∧
       ((∀ (t : Prop) (a : Int), ∃ b : Prop, R a (f (t ∧ b) x) (¬t)) ∧ namedTrue p) ∧
       ((∀ (b : Prop) (y : Int), (b ∧ y = x) → R x x p) ∧
         (∀ (_unused : Int) (_flag : Prop), p) ∧ (∃ _unused : Prop, ∃ _value : Int, p)) ∧
       f (∃ y : Int, y = x) x = f (∀ y : Int, R x y p) 0 ∧
       ((∀ z : Int, R z x p) ∧ (∃ z : Int, R z x p))) → False)
  let quantified ← IO.FS.readFile "tests/translation/quantifiers/quantified.smt2"
  for status in #["", "sat", "unsat", "unknown"] do
    let metadata := if status.isEmpty then "" else s!"(set-info :status {status})\n"
    runQuery env s!"quantified ({status})" (metadata ++ quantified) fun query =>
      checkRefutation query q(∀ P : Int → Prop, ((∀ x : Int, P x) ∧ (∃ x : Int, ¬P x)) → False)
  IO.println "Translation passed: 22 refutations and generated files; existing proof work preserved"
