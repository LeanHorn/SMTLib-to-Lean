import Smt2Lean.Pipeline
import Lean.Elab.Frontend

open Lean Meta Qq Classical
open Smt2Lean.Backend Smt2Lean.Translate Smt2Lean.Emit

local notation "smtDiv" => (fun (zero : Int → Int) (x y : Int) => ite (y = 0) (zero x) (x / y))
local notation "smtRealDiv" => (fun (zero : Real → Real) (x y : Real) => ite (y = 0) (zero x) (x / y))
local notation "smtMod" => (fun (zero : Int → Int) (x y : Int) => ite (y = 0) (zero x) (x % y))
local notation "smtShl" => (fun {w : Nat} (x y : BitVec w) => x <<< min (BitVec.toNat y) w)
local notation "smtLshr" => (fun {w : Nat} (x y : BitVec w) => x >>> min (BitVec.toNat y) w)
local notation "smtAshr" => (fun {w : Nat} (x y : BitVec w) => BitVec.sshiftRight x (min (BitVec.toNat y) w))

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
  for ref in assertions do
    unless ref.names.isEmpty || source.contains ref.namedContext do
      throwError "generated output lost assertion labels"
  let [statements, proofs] := source.splitOn "-- Proofs\n"
    | throwError "expected one Statements section followed by Proofs"
  unless (statements.startsWith "import Init\n\n-- Statements\n\n" ||
      statements.startsWith "import Mathlib.Data.Real.Basic\n\n-- Statements\n\n" ||
      statements.startsWith "import Mathlib.Algebra.Order.Archimedean.Real.Basic\n\n-- Statements\n\n") &&
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

private def checkAxioms (name : Name) (usesClassical : Bool)
    (extraAxioms : Array Name := #[]) : CoreM Unit := do
  let expected := (if usesClassical then #[``propext, ``Classical.choice, ``Quot.sound] else #[]) ++ extraAxioms
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

/-- Compare each let expansion independently, so contradictory assertions cannot hide mistakes. -/
private def checkLetBindings (env : Environment) : IO Unit := do
  let path := "tests/translation/bindings/simultaneous.smt2"
  runQuery env path (← IO.FS.readFile path) fun query => do
    withAssertions query fun parameters assertions => do
      let #[x, p] := parameters | throwError "let bindings became query parameters"
      let x : Q(Int) := x
      let p : Q(Prop) := p
      let expected : Array Expr := #[q($x = 1), q($x = 1), q($p = False),
        q(($x + 1 = $x) ∧ ((¬$p) = $p)), q($p = ($x > 0)),
        q((($x + 1) + ($x + 1) = $x + 2) ∧ ((¬$p) = $p)),
        q(∀ (a : Int) (b : Prop), (a + 1 = $x) ∧ ((¬b) = $p)),
        q(∀ (a : Int) (b : Prop), (∃ (c : Int) (d : Prop), c = a ∧ d = b) ∧ a = a ∧ b = b),
        q((True = ((1 : Int) > 0)) ∧ (False = ((2 : Int) > 0)) ∧ ($p = ($x > 0)))]
      unless assertions.size == expected.size do throwError "wrong let assertion count"
      for actual in assertions, wanted in expected do
        checkEqual actual wanted
    checkRefutation query q(∀ (x : Int) (p : Prop),
      (x = 1 ∧ x = 1 ∧ p = False ∧ ((x + 1 = x) ∧ ((¬p) = p)) ∧ p = (x > 0) ∧
        (((x + 1) + (x + 1) = x + 2) ∧ ((¬p) = p)) ∧
        (∀ (a : Int) (b : Prop), (a + 1 = x) ∧ ((¬b) = p)) ∧
        (∀ (a : Int) (b : Prop), (∃ (c : Int) (d : Prop), c = a ∧ d = b) ∧ a = a ∧ b = b) ∧
        ((True = ((1 : Int) > 0)) ∧ (False = ((2 : Int) > 0)) ∧ (p = (x > 0)))) → False)
  IO.println "Let bindings passed: 9 Bool/Int assertions match handwritten expansions and emitted propositions"

private def checkDefinitions (env : Environment) : IO Unit := do
  let path := "tests/translation/bindings/definitions.smt2"
  runQuery env path (← IO.FS.readFile path) fun query => do
    withAssertions query fun parameters assertions => do
      let #[x, p, f, later] := parameters | throwError "definitions became free parameters"
      let x : Q(Int) := x
      let p : Q(Prop) := p
      let f : Q(Int → Int) := f
      let later : Q(Int) := later
      let expected : Array Expr := #[
        q($x + 1 = $x + 1), q(($x + 1) + 1 = $f $x),
        q((if $p then ($x + 1) + 1 else $x + 1) = (if $p then ($x + 1) + 1 else $x + 1)),
        q(∀ (a : Int) (_b : Prop), ($p ∧ a > $x + 1) = ($p ∧ a > $x + 1)),
        q((if False then (99 : Int) + 1 else $x + 1) = $x + 1),
        q(∀ y : Int, ∃ z : Int, y = z), q(∀ q r : Prop, q = r),
        q(($later + 1) + 1 = ($later + 1) + 1)]
      unless assertions.size == expected.size do throwError "wrong definition assertion count"
      for actual in assertions, wanted in expected do checkEqual actual wanted
    checkRefutation query (usesClassical := true) q(∀ (x : Int) (p : Prop) (f : Int → Int) (later : Int),
      (x + 1 = x + 1 ∧ (x + 1) + 1 = f x ∧
        (if p then (x + 1) + 1 else x + 1) = (if p then (x + 1) + 1 else x + 1) ∧
        (∀ (a : Int) (_b : Prop), (p ∧ a > x + 1) = (p ∧ a > x + 1)) ∧
        (if False then (99 : Int) + 1 else x + 1) = x + 1 ∧
        (∀ y : Int, ∃ z : Int, y = z) ∧ (∀ q r : Prop, q = r) ∧
        (later + 1) + 1 = (later + 1) + 1) → False)
  runQuery env "closed definition"
    "(set-logic QF_UF) (define-fun yes () Bool true) (assert yes) (check-sat)"
    fun query => checkRefutation query q(True → False)
  IO.println "Definitions passed: Bool/Int bodies, aliases, chains, shadowing, and capture-free substitution"

private def checkNamedAssertions (env : Environment) : IO Unit := do
  let path := "tests/translation/bindings/named.smt2"
  runQuery env path (← IO.FS.readFile path) fun query => do
    withAssertions query fun parameters assertions => do
      let #[x, p] := parameters | throwError "named terms became query parameters"
      let x : Q(Int) := x
      let p : Q(Prop) := p
      let expected : Array Expr := #[q($x + 1 > 0), q(¬($x + 1 > 0)), q($x + 1 > 0),
        q($x = 1 ∧ $x = 1 ∧ $x = 1),
        q(∀ (_a : Int) (_b : Prop), ($x + 1 > 0) = ($x + 1 > 0)),
        q(($x + 1 = $x + 1) ∧ ($x + 1 = $x + 1)), q($p ∧ $p ∧ $p)]
      unless assertions.size == expected.size do throwError "wrong named assertion count"
      for actual in assertions, wanted in expected do checkEqual actual wanted
    checkRefutation query q(∀ (x : Int) (p : Prop),
      (x + 1 > 0 ∧ ¬(x + 1 > 0) ∧ x + 1 > 0 ∧ (x = 1 ∧ x = 1 ∧ x = 1) ∧
        (∀ (_a : Int) (_b : Prop), (x + 1 > 0) = (x + 1 > 0)) ∧
        ((x + 1 = x + 1) ∧ (x + 1 = x + 1)) ∧ (p ∧ p ∧ p)) → False)
  IO.println "Named assertions passed: aliases, shadowing, duplicate bodies, and escaped source labels"

private def checkQuantifierHints (env : Environment) : IO Unit := do
  let path := "tests/translation/quantifiers/hints.smt2"
  runQuery env path (← IO.FS.readFile path) fun query => do
    let expected ← withAssertions query fun parameters assertions => do
      let #[x, p, r] := parameters | throwError "hints became query parameters"
      let x : Q(Int) := x
      let p : Q(Int → Prop) := p
      let r : Q(Int → Prop → Prop) := r
      let a : Q(Prop) := q(∀ y : Int, $p y)
      let b : Q(Prop) := q(∀ y : Int, ∃ (z : Int) (flag : Prop), y = z ∧ $r z flag)
      let c : Q(Prop) := q((∀ flag : Prop, $r $x flag) ∧ (∀ flag : Prop, $r $x flag))
      let d : Q(Prop) := q(∀ (y : Int) (flag : Prop), $r y flag)
      let pairs : Array Expr := #[a, b, c, d, a]
      unless assertions.size == 2 * pairs.size do throwError "wrong hint assertion count"
      for wanted in pairs, i in [:pairs.size] do
        checkEqual assertions[2 * i]! wanted
        checkEqual assertions[2 * i + 1]! wanted
      mkForallFVars parameters q(($a ∧ $a ∧ $b ∧ $b ∧ $c ∧ $c ∧ $d ∧ $d ∧ $a ∧ $a) → False)
        (usedOnly := false)
    checkRefutation query expected
  IO.println "Quantifier hints passed: 5 annotated/plain pairs match handwritten propositions"

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
          $r (if b then x else y) (if c then b else x < y) (if x < y then x + 1 else y)),
        q(∀ (x : Int) (b : Prop), $p x → x + 1 > x → ¬b → $r ((x + 1) + (x + 1)) b x),
        q(∀ (outerX : Int) (outerB : Prop) (innerX : Int) (innerB : Prop),
          $p outerX → innerX + 1 > outerX → innerB = outerB → $r (innerX + 1) outerB outerX)
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
  IO.println "CHC reconstruction passed: 19 clauses match handwritten Lean propositions"

private def checkProblem (problem : Smt2Lean.Chc.Problem) (expected : Expr)
    (usesClassical : Bool := false) (extraAxioms : Array Name := #[]) : MetaM Unit := do
  let value ← defineProblem problem
  if value.hasFVar || value.hasMVar || value.hasLooseBVars then
    throwError "Problem contains unresolved variables"
  checkEqual value expected
  let .defnInfo definition ← getConstInfo `Problem
    | throwError "expected a definition named Problem"
  checkEqual definition.type q(Prop)
  checkEqual definition.value value
  checkAxioms `Problem usesClassical extraAxioms
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
    let plain := input.replace "(set-info :status sat)" metadata
    let configured := "(set-option :produce-models true)\n(set-option :produce-proofs true)\n" ++
      "(set-option :produce-unsat-cores true)\n(set-option :print-success true)\n" ++
      "(set-option :random-seed 42)\n" ++ plain
    for text in #[plain, configured] do
      runProblem env s!"{path} ({status})" text fun problem => checkProblem problem expected
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
        r (if b then x else y) (if c then b else x < y) (if x < y then x + 1 else y)) ∧
      (∀ (x : Int) (b : Prop), p x → x + 1 > x → ¬b → r ((x + 1) + (x + 1)) b x) ∧
      (∀ (outerX : Int) (outerB : Prop) (innerX : Int) (innerB : Prop),
        p outerX → innerX + 1 > outerX → innerB = outerB → r (innerX + 1) outerB outerX))
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
  let path := "tests/translation/chc/definitions.smt2"
  let input ← IO.FS.readFile path
  let hinted := input.replace "(=> |entry clause| (rule x b))"
    "(! (=> |entry clause| (rule x b)) :pattern ((P x) (R x b)) :no-pattern (P (^ x 2)) :qid step)"
    |>.replace "(=> (bad x b) false)" "(! (=> (bad x b) false) :pattern ((R x b)) :qid safety)"
  for text in #[input, hinted] do
    runProblem env path text fun problem => do
      withClauses problem fun parameters clauses => do
        let #[p, r] := parameters | throwError "CHC helpers or hints became existential relations"
        let p : Q(Int → Prop) := p
        let r : Q(Int → Prop → Prop) := r
        checkClauseValues parameters clauses #[q($p 0),
          q(∀ (x : Int) (b : Prop), $p 0 → $p x → x > 0 → $r (if b then x + 1 else x) b),
          q(∀ (x : Int) (b : Prop), $r x b → x > 10 → b → False)]
      checkProblem problem (usesClassical := true) q(∃ (p : Int → Prop) (r : Int → Prop → Prop),
        p 0 ∧ (∀ (x : Int) (b : Prop), p 0 → p x → x > 0 → r (if b then x + 1 else x) b) ∧
        (∀ (x : Int) (b : Prop), r x b → x > 10 → b → False))
  IO.println "CHC problems passed: 16 complete propositions and emitted definitions; axiom dependencies checked"

/-- Compare signed arithmetic with a quotient/remainder search using only +, *, and order. -/
private def checkDivision (env : Environment) : IO Unit := do
  let numeral (n : Int) := if n < 0 then s!"(- {n.natAbs})" else toString n
  let mut cases : Array String := #[]
  for i in [:17] do
    let m := (i : Int) - 8
    for j in [:9] do
      let n := (j : Int) - 4
      if n == 0 then continue
      let mut result : Option (Int × Int) := none
      for k in [:19] do
        let q := (k : Int) - 9
        let r := m - n * q
        if 0 ≤ r && r < (n.natAbs : Int) then result := some (q, r)
      let some (q, r) := result | throw (IO.userError "Euclidean witness search failed")
      cases := cases ++ #[s!"(= (div {numeral m} {numeral n}) {numeral q})",
        s!"(= (mod {numeral m} {numeral n}) {numeral r})"]
  cases := cases ++ #[
    "(= (div 340282366920938463463374607431768211457 2) 170141183460469231731687303715884105728)",
    "(= (mod 340282366920938463463374607431768211457 (- 2)) 1)",
    "(= (div (- 340282366920938463463374607431768211457) 2) (- 170141183460469231731687303715884105729))",
    "(= (mod (- 340282366920938463463374607431768211457) (- 2)) 1)",
    "(= (div 100 3 (- 2)) (- 16))"]
  let input := "(set-logic ALL)" ++ String.join (cases.toList.map (s!"(assert {·})")) ++ "(check-sat)"
  runQuery env "Euclidean division" input fun query =>
    withAssertions query fun parameters assertions => do
      unless parameters.isEmpty && assertions.size == cases.size do
        throwError "literal nonzero divisors introduced interpretations or lost assertions"
      for value in assertions do
        checkWithKernel (← mkDecideProof value)
  let path := "tests/translation/int/division.smt2"
  runQuery env path (← IO.FS.readFile path) fun query => do
    checkFunctionIsolation query
    checkRefutation query (usesClassical := true) q(
      ∀ (d m : Int → Int) (x y : Int) (flag : Prop) (f namedD namedM : Int → Int),
        ((-5 : Int) / 2 = -3 ∧ (5 : Int) / -2 = -2 ∧ (-5 : Int) % -2 = 1 ∧
          (100 : Int) / 3 / -2 = -16 ∧
          smtMod m (smtDiv d x y) y = smtMod m (smtDiv d x y) y ∧
          smtDiv d x 0 = smtDiv d (x + 0) 0 ∧ smtMod m x 0 = smtMod m (x + 0) 0 ∧
          smtDiv d (smtDiv d x 0) 0 = f (smtMod m x 0) ∧
          (∀ x : Int, ∃ y : Int, smtDiv d x y = smtMod m x y) ∧
          (if flag then smtDiv d x y else smtMod m x y) = f (x / 2) ∧ namedD x = namedM x) → False)
  -- Constants of the same spelling as internal keys remain separate native bindings.
  runQuery env "division binder shadowing"
    "(set-logic ALL)(declare-const |SMT.divZero| Int)(assert (forall ((divZero Int)) (= (div divZero 0) |SMT.divZero|)))(check-sat)"
    fun query => checkRefutation query q(∀ (d : Int → Int) (x : Int),
      (∀ y : Int, smtDiv d y 0 = x) → False)
  -- A nonzero literal needs no arbitrary interpretation, even through a definition.
  runQuery env "nonzero definition"
    "(set-logic ALL)(define-fun two () Int (- 2))(declare-const x Int)(assert (= (div x two) (mod x two)))(check-sat)"
    fun query => checkRefutation query q(∀ x : Int, x / -2 = x % -2 → False)
  runQuery env "division assumptions"
    "(set-logic ALL)(declare-const x Int)(define-fun p () Bool (= (div x 0) 7))(check-sat-assuming (p))"
    fun query => checkRefutation query q(∀ (d : Int → Int) (x : Int), smtDiv d x 0 = 7 → False)
  runQuery env "mixed division chain"
    "(set-logic ALL)(assert (= (div 100 3 0 (- 2)) 7))(check-sat)"
    fun query => checkRefutation query q(∀ d : Int → Int, smtDiv d (100 / 3) 0 / -2 = 7 → False)
  runQuery env "signed zero divisors"
    "(set-logic ALL)(declare-const x Int)(assert (= (div x (- 0)) (mod x (- (- 0)))))(check-sat)"
    fun query => checkRefutation query q(∀ (d m : Int → Int) (x : Int), smtDiv d x 0 = smtMod m x 0 → False)
  let path := "tests/translation/chc/division.smt2"
  runProblem env path (← IO.FS.readFile path) fun problem =>
    checkProblem problem q(∃ A : Type, Nonempty A ∧ ∃ (d m : Int → Int)
      (p : A → Int → Prop) (r : A → Int → Int → Prop),
      (∀ (a : A) (x : Int), x / 2 = 0 → p a (x % -2)) ∧
      (∀ (a : A) (x y : Int), p a x → smtDiv d x y = 7 → smtMod m x y = 3 →
        r a (smtDiv d x 0) (smtMod m x 0)) ∧
      (∀ (a : A) (x : Int), r a (smtDiv d x 0) (smtMod m x 0) →
        smtDiv d x 0 ≠ smtDiv d (x + 0) 0 → False))
  IO.println s!"Division passed: {cases.size} exact signed/large arithmetic cases; shared zero interpretations and SMT/CHC closure"

/-- Real carriers, exact rationals, and zero interpretations survive emission and scopes. -/
private def checkReals (env : Environment) : IO Unit := do
  let path := "tests/translation/real/arithmetic.smt2"
  runQuery env path (← IO.FS.readFile path) fun query => do
    checkFunctionIsolation query
    checkRefutation query (usesClassical := true) q(
      ∀ A : Type, Nonempty A → ∀ (d : Real → Real) (x y : Real) (b : Prop) (i : Int)
        (a : A) (f : Real → Real) (g : Real → Prop → Int → A → Real) (named : Real → Real),
      ((1 / 10 : Real) + 1 / 5 = 3 / 10 ∧
        ((x ≤ y ∧ y ≤ 3) ∧ (x < y ∧ y < 4) ∧ (y ≥ x ∧ x ≥ 0) ∧ y > x ∧ x > -1) ∧
        (x ≠ y ∧ x ≠ 1 / 3 ∧ y ≠ 1 / 3) ∧ (if b then x else y) = f (1 / 3) ∧
        x + 1 / 2 - x = 1 / 2 ∧ (∀ x : Real, ∃ y : Real, smtRealDiv d x 0 = smtRealDiv d y 0) ∧
        smtRealDiv d x y = f (x + 1 / 10) ∧ smtRealDiv d x 0 = smtRealDiv d (x + 0) (-0) ∧
        named x = smtRealDiv d x 0 ∧ g x b i a = f x ∧ (x + 1 = x + 1 ∧ i + 1 = i) ∧
        (∃ root : Real, root * root = 2)) → False)
  for logic in #["QF_LRA", "QF_NRA", "QF_UFLRA", "QF_UFNRA", "LRA", "NRA", "UFLRA", "UFNRA", "ALL"] do
    runQuery env logic s!"(set-logic {logic})(declare-const x Real)(assert (< 1 x))(assert (= (/ (- 1) 3) x))(check-sat)"
      fun query => checkRefutation query (usesClassical := true)
        q(∀ x : Real, (1 < x ∧ -1 / 3 = x) → False)
  runQuery env "Real type-name shadowing"
    "(set-logic ALL)(assert (forall ((Real Real) (Int Int)) (and (= (+ Real 1) 2.0) (= Int 0))))(check-sat)"
    fun query => checkRefutation query (usesClassical := true)
      q((∀ (x : Real) (i : Int), x + 1 = 2 ∧ i = 0) → False)
  runQuery env "Real definition shadowing"
    "(set-logic ALL)(declare-const x Real)(define-fun offset ((y Real)) Real (+ x y))(assert (forall ((x Real)) (= (offset x) x)))(check-sat)"
    fun query => checkRefutation query (usesClassical := true)
      q(∀ x : Real, (∀ y : Real, x + y = y) → False)
  runQuery env "independent integer and Real zero cases"
    "(set-logic ALL)(assert (and (= (div 1 0) 7) (= (mod 1 0) 8) (= (/ 1 0) 9.0)))(check-sat)"
    fun query => checkRefutation query (usesClassical := true)
      q(∀ (d m : Int → Int) (r : Real → Real),
        (smtDiv d 1 0 = 7 ∧ smtMod m 1 0 = 8 ∧ smtRealDiv r 1 0 = 9) → False)
  let path := "tests/translation/chc/real.smt2"
  runProblem env path (← IO.FS.readFile path) fun problem =>
    checkProblem problem (usesClassical := true) q(∃ A : Type, Nonempty A ∧ ∃ (d : Real → Real)
      (p : A → Real → Prop) (r : A → Real → Prop → Int → Prop),
      (∀ (a : A) (x : Real), x = 1 / 10 → p a x) ∧
      (∀ (a : A) (x y : Real) (b : Prop) (i : Int), p a x → x < y → y / 2 = x →
        smtRealDiv d x y = 1 / 2 → r a (if b then smtRealDiv d x 0 else x + 1 / 10) b i) ∧
      (∀ (a : A) (x : Real) (b : Prop) (i : Int), r a (smtRealDiv d x 0) b i →
        smtRealDiv d x 0 ≠ smtRealDiv d (x + 0) 0 → False))
  let source ← Smt2Lean.Pipeline.translateSession
    "(set-logic ALL)(check-sat)(push 1)(declare-const x Real)\
     (define-fun p () Bool (= (/ x 0.0) 7.0))(check-sat-assuming (p))(check-sat)\
     (pop 1)(check-sat)(reset)(set-logic HORN)\
     (assert (=> (= (/ 1.0 0.0) 7.0) false))(check-sat)" env
  unless source.startsWith "import Mathlib.Data.Real.Basic" &&
      (source.splitOn "noncomputable def SMT.realDiv ").length == 2 do
    throw (IO.userError "Real session lost its import or duplicated its helper")
  unsafe enableInitializersExecution
  let some emitted ← Elab.runFrontend source
      (({} : Options).setBool `Elab.async false) "Query.lean" `Query
    | throw (IO.userError "Real session did not elaborate")
  let check : MetaM Unit := do
    for (name, expected) in #[
      (`Refutation_1, q(True → False)),
      (`Refutation_2, q(∀ (d : Real → Real) (x : Real), smtRealDiv d x 0 = 7 → False)),
      (`Refutation_3, q(∀ _x : Real, True → False)),
      (`Refutation_4, q(True → False)),
      (`Problem_5, q(∃ d : Real → Real, smtRealDiv d 1 0 = 7 → False))
    ] do
      let .defnInfo definition ← getConstInfo name | throwError "missing {name}"
      checkEqual (← deltaExpand definition.value Smt2Lean.Helpers.isHelper) expected
      checkStatementAxioms name
  discard <| check.toIO { fileName := "Real session", fileMap := default } { env := emitted }
  let core ← Smt2Lean.Pipeline.translateSession
    "(set-logic ALL)(push 1)(declare-const unused Real)(pop 1)(check-sat)" env
  unless core.startsWith "import Init" do
    throw (IO.userError "a popped Real declaration changed the output profile")
  IO.println "Real translation passed: exact arithmetic, SMT/CHC targets, numeral coercions, and five scoped snapshots"

/-- Casts preserve Int subterms; floor and integrality survive binders and emission. -/
private def checkConversions (env : Environment) : IO Unit := do
  let path := "tests/translation/real/conversions.smt2"
  runQuery env path (← IO.FS.readFile path) fun query => do
    checkFunctionIsolation query
    checkRefutation query (usesClassical := true) q(
      ∀ (d m : Int → Int) (r : Real → Real) (i : Int) (x : Real) (b : Prop) (f : Real → Int),
      (((i + 1 : Int) : Real) = (i : Real) + 1 ∧
        ((i : Real) < x ∧ x ≤ (i : Real) ∧ ((i + 1 : Int) : Real) > x ∧ x ≥ ((i - 1 : Int) : Real)) ∧
        (i : Real) / 2 = (i : Real) * x - (i : Real) ∧
        (i + 1 = Int.floor x ∧ ((i + 1 : Int) : Real) + x = (i : Real) + 1 / 2) ∧
        (Int.floor (- (17 / 10 : Real)) = -2 ∧ Int.floor (- (2 : Real)) = -2) ∧
        (x = (Int.floor x : Real)) = (x = (Int.floor x : Real)) ∧
        Int.floor (i : Real) = i ∧ (Int.floor (i : Real) = i ∧ (i : Real) = (Int.floor (i : Real) : Real)) ∧
        (if b then Int.floor x else i) = f (i : Real) ∧
        (Int.floor x : Real) = (i : Real) + 1 / 2 ∧
        (∀ (_i : Int) (x : Real), ∃ y : Real, y = (Int.floor x : Real) ∧ y = (Int.floor y : Real)) ∧
        ((smtDiv d i 0 : Real) = smtRealDiv r (i : Real) 0 ∧
          Int.floor (smtRealDiv r x 0) = smtMod m i 0)) → False)
  for logic in #["QF_LIRA", "QF_NIRA", "QF_UFLIRA", "QF_UFNIRA", "LIRA", "NIRA", "UFLIRA", "UFNIRA"] do
    runQuery env logic s!"(set-logic {logic})(declare-const i Int)(declare-const x Real)\
      (assert (= (to_real i) x))(assert (= (to_int x) i))(assert (is_int x))(check-sat)"
      fun query => checkRefutation query (usesClassical := true)
        q(∀ (i : Int) (x : Real), ((i : Real) = x ∧ Int.floor x = i ∧ x = (Int.floor x : Real)) → False)
  runQuery env "conversion type-name shadowing"
    "(set-logic ALL)(assert (forall ((Real Real) (Int Int)) (= (to_int Real) Int)))(check-sat)"
    fun query => checkRefutation query (usesClassical := true)
      q((∀ (x : Real) (i : Int), Int.floor x = i) → False)
  let path := "tests/translation/chc/conversions.smt2"
  runProblem env path (← IO.FS.readFile path) fun problem =>
    checkProblem problem (usesClassical := true) q(∃ A : Type, Nonempty A ∧
      ∃ (d : Int → Int) (r : Real → Real) (p : A → Int → Real → Prop) (s : A → Real → Int → Prop → Prop),
      (∀ (a : A) (i : Int), p a i (i : Real)) ∧
      (∀ (a : A) (i : Int) (x : Real) (b : Prop), p a i x → (i : Real) < x →
        x = (Int.floor x : Real) → s a ((i : Real) + x) (Int.floor (smtRealDiv r x 0)) b) ∧
      (∀ (a : A) (x : Real) (i : Int) (b : Prop), s a x i b → ¬i = Int.floor x →
        (smtDiv d i 0 : Real) = smtRealDiv r x 0 → False))
  let source ← Smt2Lean.Pipeline.translateSession
    "(set-logic ALL)(declare-const i Int)(push 1)(declare-const x Real)\
     (define-fun p () Bool (= (to_int x) i))(check-sat-assuming (p))(check-sat)\
     (pop 1)(check-sat)(reset)(set-logic HORN)\
     (assert (=> (not (is_int (to_real 3))) false))(check-sat)" env
  unless source.startsWith "import Mathlib.Algebra.Order.Archimedean.Real.Basic" do
    throw (IO.userError "mixed session lost its floor import")
  unsafe enableInitializersExecution
  let some emitted ← Elab.runFrontend source
      (({} : Options).setBool `Elab.async false) "Query.lean" `Query
    | throw (IO.userError "mixed session did not elaborate")
  let check : MetaM Unit := do
    for (name, expected) in #[
      (`Refutation_1, q(∀ (i : Int) (x : Real), Int.floor x = i → False)),
      (`Refutation_2, q(∀ (_i : Int) (_x : Real), True → False)),
      (`Refutation_3, q(∀ _i : Int, True → False)),
      (`Problem_4, q(¬(3 : Real) = (Int.floor (3 : Real) : Real) → False))
    ] do
      let .defnInfo definition ← getConstInfo name | throwError "missing {name}"
      checkEqual definition.value expected
      checkStatementAxioms name
  discard <| check.toIO { fileName := "mixed session", fileMap := default } { env := emitted }
  for body in #["(push 1)(assert (is_int 0.0))(pop 1)", "(assert (is_int 0.0))(reset-assertions)"] do
    let core ← Smt2Lean.Pipeline.translateSession s!"(set-logic ALL){body}(check-sat)" env
    unless core.startsWith "import Init" do
      throw (IO.userError "discarded conversions changed the output profile")
  IO.println "Mixed arithmetic passed: casts, floor, integrality, SMT/CHC targets, and scoped snapshots"

/-- Reference bit operations use individual binary digits, independently of BitVec. -/
private def bitwiseReference (width x y : Nat) (op : Bool → Bool → Bool) : Nat := Id.run do
  let mut result := 0
  for i in [:width] do
    let place := 2 ^ i
    if op (x / place % 2 == 1) (y / place % 2 == 1) then result := result + place
  return result

/-- Exhaustive tiny widths and wide boundaries, checked as closed kernel proofs. -/
private def checkBitvectorValues (env : Environment) : IO Unit := do
  let mut total := 0
  for width in #[1, 2, 3, 4, 32, 64, 129] do
    let modulus := 2 ^ width
    let half := modulus / 2
    let values := if width ≤ 4 then (List.range modulus).toArray
      else #[0, 1, half - 1, half, modulus - 1]
    let literal (n : Nat) := s!"(_ bv{n} {width})"
    let signed (n : Nat) : Int := if n < half then (n : Int) else (n : Int) - modulus
    let mut rows : Array String := #[]
    for x in values do
      rows := rows.push s!"(and (= (bvneg {literal x}) {literal ((modulus - x) % modulus)}) \
        (= (bvnot {literal x}) {literal (modulus - 1 - x)}))"
      total := total + 2
      for y in values do
        let a := literal x
        let b := literal y
        let andValue := bitwiseReference width x y (· && ·)
        let orValue := bitwiseReference width x y (· || ·)
        let xorValue := bitwiseReference width x y (· != ·)
        let mut checks := #[
          s!"(= (bvadd {a} {b}) {literal ((x + y) % modulus)})",
          s!"(= (bvsub {a} {b}) {literal ((x + modulus - y) % modulus)})",
          s!"(= (bvmul {a} {b}) {literal ((x * y) % modulus)})"]
        for (op, result) in #[
          ("bvand", andValue), ("bvor", orValue), ("bvxor", xorValue),
          ("bvnand", modulus - 1 - andValue), ("bvnor", modulus - 1 - orValue),
          ("bvxnor", modulus - 1 - xorValue)
        ] do checks := checks.push s!"(= ({op} {a} {b}) {literal result})"
        for (op, truth) in #[
          ("bvult", decide (x < y)), ("bvule", decide (x ≤ y)), ("bvugt", decide (x > y)), ("bvuge", decide (x ≥ y)),
          ("bvslt", decide (signed x < signed y)), ("bvsle", decide (signed x ≤ signed y)),
          ("bvsgt", decide (signed x > signed y)), ("bvsge", decide (signed x ≥ signed y))
        ] do
          let test := s!"({op} {a} {b})"
          checks := checks.push (if truth then test else s!"(not {test})")
        checks := checks.push s!"(= (bvcomp {a} {b}) {if x == y then "#b1" else "#b0"})"
        total := total + checks.size
        rows := rows.push ("(and " ++ String.intercalate " " checks.toList ++ ")")
    let input := "(set-logic QF_BV)" ++ String.join (rows.toList.map (s!"(assert {·})")) ++ "(check-sat)"
    runQuery env s!"bitvector width {width}" input fun query =>
      withAssertions query fun parameters assertions => do
        unless parameters.isEmpty && assertions.size == rows.size do
          throwError "closed BV values introduced parameters or lost assertions"
        for value in assertions do
          checkWithKernel (← mkDecideProof (← deltaExpand value Smt2Lean.Helpers.isHelper))
  IO.println s!"Bitvector values passed: {total} kernel-checked cases; exhaustive widths 1–4 and 32/64/129-bit boundaries"

private def checkBitvectors (env : Environment) : IO Unit := do
  checkBitvectorValues env
  let path := "tests/translation/bitvec/arithmetic.smt2"
  runQuery env path (← IO.FS.readFile path) fun query => do
    checkFunctionIsolation query
    checkRefutation query (usesClassical := true) q(∀ A : Type, Nonempty A →
      ∀ (x y : BitVec 4) (b : Prop) (a : A) (f : BitVec 4 → BitVec 4)
        (g : A → BitVec 4 → Prop → Int → BitVec 8) (named : BitVec 4 → BitVec 4 → BitVec 1),
      (((15 : BitVec 4) = 15 ∧ (15 : BitVec 4) = 15) ∧
        x + y + 1 = x - -y ∧ x * y * 2 = -(~~~x) ∧
        x &&& y &&& 15 = x ||| y ||| 0 ∧ x ^^^ y ^^^ 1 = ~~~(x &&& y) ∧
        ~~~(x ||| y) = ~~~(x ^^^ y) ∧
        (x < y ∧ x ≤ y ∧ y > x ∧ y ≥ x) ∧
        (BitVec.slt x y = true ∧ BitVec.sle x y = true ∧ BitVec.slt x y = true ∧ BitVec.sle x y = true) ∧
        (BitVec.ofBool (x == y) = 1 ∧ BitVec.ofBool (x == x) = named x y) ∧
        (x ≠ y ∧ x ≠ 0 ∧ y ≠ 0) ∧ (if b then x + 1 else y) = f (if x < y then x else y) ∧
        g a x b 7 = 128 ∧ (y + 1) - (x + 1) = 0 ∧
        (∀ _x : BitVec 4, ∃ z : BitVec 8, z = g a y b 0) ∧
        (∀ x : BitVec 4, ~~~x = ~~~x) ∧
        (340282366920938463463374607431768211457 : BitVec 129) = 340282366920938463463374607431768211457) → False)
  for logic in #["QF_BV", "QF_UFBV", "BV", "UFBV"] do
    runQuery env logic s!"(set-logic {logic})(declare-const x (_ BitVec 8))\
      (assert (= (bvadd x #x01) #x00))(check-sat)"
      fun query => checkRefutation query q(∀ x : BitVec 8, x + 1 = 0 → False)
  runQuery env "BV type-name shadowing"
    "(set-logic ALL)(assert (forall ((Nat (_ BitVec 4)) (BitVec (_ BitVec 4)))\
     (= (bvadd Nat BitVec #x1) #x0)))(check-sat)"
    fun query => checkRefutation query
      q((∀ x y : BitVec 4, x + y + 1 = 0) → False)
  runQuery env "mixed Real/BV signature"
    "(set-logic ALL)(declare-fun f ((_ BitVec 8) Real Int Bool) (_ BitVec 4))\
     (declare-const x (_ BitVec 8))(assert (= (f x 0.5 7 true) #xf))(check-sat)"
    fun query => checkRefutation query (usesClassical := true)
      q(∀ (f : BitVec 8 → Real → Int → Prop → BitVec 4) (x : BitVec 8), f x (1 / 2) 7 True = 15 → False)
  let path := "tests/translation/chc/bitvec.smt2"
  runProblem env path (← IO.FS.readFile path) fun problem =>
    checkProblem problem (usesClassical := true) q(∃ A : Type, Nonempty A ∧
      ∃ (p : A → BitVec 4 → Prop) (r : A → BitVec 4 → BitVec 1 → Prop → Prop),
      (∀ a : A, p a 0) ∧
      (∀ (a : A) (x : BitVec 4) (b : Prop), p a x → x < 15 → BitVec.sle 0 x = true →
        r a (if b then x + 1 else ~~~x) (BitVec.ofBool (x == 15)) b) ∧
      (∀ (a : A) (x : BitVec 4) (bit : BitVec 1) (b : Prop), r a x bit b → bit = 0 → x ≠ 0 → p a (x &&& 14)) ∧
      (∀ (a : A) (x : BitVec 4), p a x → x < 0 → False))
  let source ← Smt2Lean.Pipeline.translateSession
    "(set-logic ALL)(declare-const x (_ BitVec 4))(push 1)\
     (define-fun p () Bool (= (bvcomp x #xf) #b1))(check-sat-assuming (p))(check-sat)\
     (pop 1)(check-sat)(reset)(set-logic HORN)(declare-fun P ((_ BitVec 8)) Bool)\
     (assert (P #xff))(check-sat)" env
  unless source.startsWith "import Init" && (source.splitOn "def SMT.bvcomp ").length == 2 do
    throw (IO.userError "BV session changed the core profile or duplicated its helper")
  unsafe enableInitializersExecution
  let some emitted ← Elab.runFrontend source
      (({} : Options).setBool `Elab.async false) "Query.lean" `Query
    | throw (IO.userError "BV session did not elaborate")
  let check : MetaM Unit := do
    for (name, expected) in #[
      (`Refutation_1, q(∀ x : BitVec 4, BitVec.ofBool (x == 15) = 1 → False)),
      (`Refutation_2, q(∀ _x : BitVec 4, True → False)),
      (`Refutation_3, q(∀ _x : BitVec 4, True → False)),
      (`Problem_4, q(∃ p : BitVec 8 → Prop, p 255))
    ] do
      let .defnInfo definition ← getConstInfo name | throwError "missing {name}"
      checkEqual (← deltaExpand definition.value Smt2Lean.Helpers.isHelper) expected
      checkStatementAxioms name
  discard <| check.toIO { fileName := "BV session", fileMap := default } { env := emitted }
  IO.println "Bitvector translation passed: complete SMT/CHC targets, four logic profiles, and scoped snapshots"

/-- Width-changing operations checked against natural-number arithmetic. -/
private def checkBitvectorWidthValues (env : Environment) : IO Unit := do
  let literal (n width : Nat) := s!"(_ bv{n} {width})"
  let samples (width : Nat) := if width ≤ 4 then (List.range (2 ^ width)).toArray
    else #[0, 1, 2 ^ (width - 1) - 1, 2 ^ (width - 1), 2 ^ width - 1]
  let mut total := 0
  for width in #[1, 2, 3, 4, 32, 64, 129] do
    let mut rows : Array String := #[]
    let slices := if width ≤ 4 then Id.run do
        let mut result := #[]
        for hi in [:width] do
          for lo in [:hi + 1] do result := result.push (hi, lo)
        return result
      else #[(width - 1, 0), (0, 0), (width - 1, width - 1),
        (width - 1, width - 3), (width / 2 + 1, width / 2 - 1)]
    for x in samples width do
      let a := literal x width
      let mut checks := #[]
      for (hi, lo) in slices do
        let size := hi - lo + 1
        checks := checks.push s!"(= ((_ extract {hi} {lo}) {a}) {literal (x / 2 ^ lo % 2 ^ size) size})"
      for extra in #[0, 1, 3, 65] do
        let size := width + extra
        let signed := if x < 2 ^ (width - 1) then x else x + 2 ^ size - 2 ^ width
        checks := checks.push s!"(= ((_ zero_extend {extra}) {a}) {literal x size})"
        checks := checks.push s!"(= ((_ sign_extend {extra}) {a}) {literal signed size})"
      for copies in #[1, 2, 3] do
        let value := (List.range copies).foldl (fun n _ => n * 2 ^ width + x) 0
        checks := checks.push s!"(= ((_ repeat {copies}) {a}) {literal value (width * copies)})"
      for otherWidth in #[1, 2, 3, 64] do
        for y in samples otherWidth do
          checks := checks.push s!"(= (concat {a} {literal y otherWidth}) \
            {literal (x * 2 ^ otherWidth + y) (width + otherWidth)})"
      total := total + checks.size
      rows := rows.push ("(and " ++ String.intercalate " " checks.toList ++ ")")
    let input := "(set-logic QF_BV)" ++ String.join (rows.toList.map (s!"(assert {·})")) ++ "(check-sat)"
    runQuery env s!"bitvector width changes {width}" input fun query =>
      withAssertions query fun parameters assertions => do
        unless parameters.isEmpty && assertions.size == rows.size do
          throwError "width changes introduced parameters or lost assertions"
        for value in assertions do checkWithKernel (← mkDecideProof value)
  IO.println s!"Bitvector width values passed: {total} kernel-checked cases; widths 1–4 and 32/64/129"

private def checkBitvectorWidths (env : Environment) : IO Unit := do
  checkBitvectorWidthValues env
  let path := "tests/translation/bitvec/widths.smt2"
  runQuery env path (← IO.FS.readFile path) fun query => do
    checkFunctionIsolation query
    checkRefutation query (usesClassical := true) q(
      ∀ (x : BitVec 4) (y : BitVec 3) (p : Prop) (f : BitVec 8 → BitVec 4),
      (((x ++ y) ++ (1 : BitVec 1)) = (x ++ (y ++ (1 : BitVec 1))) ∧
        (x ++ x).extractLsb 7 4 = x ∧
        (x ++ x).extractLsb 3 0 = x ∧
        x.zeroExtend 4 = x.signExtend 4 ∧
        x.signExtend 8 = (if BitVec.slt x 0 = true then (15 : BitVec 4) ++ x else x.zeroExtend 8) ∧
        x.replicate 2 = x ++ x ∧
        f ((if p then x else 1).zeroExtend 8) = (x.replicate 3).extractLsb 6 3 ∧
        (x.zeroExtend 8).extractLsb 7 4 = 0 ∧
        (∀ _x : BitVec 4, ∃ x : BitVec 8, x.extractLsb 3 0 = 15) ∧
        (∀ x : BitVec 4, x.replicate 2 = x ++ x)) → False)
  let path := "tests/translation/chc/widths.smt2"
  runProblem env path (← IO.FS.readFile path) fun problem =>
    -- Core concat/repeat width proofs use these two foundational axioms.
    checkProblem problem (extraAxioms := #[``propext, ``Quot.sound])
      q(∃ (p : BitVec 4 → Prop) (r : BitVec 8 → BitVec 8 → BitVec 8 → Prop),
      p 15 ∧
      (∀ x : BitVec 4, p x → x.extractLsb 3 3 = 1 → r (x.zeroExtend 8) (x.signExtend 8) (x.replicate 2)) ∧
      (∀ x y z : BitVec 8, r x y z → z = (z.extractLsb 3 0 ++ z.extractLsb 3 0) → p (y.extractLsb 3 0)) ∧
      (∀ x y z : BitVec 8, r x y z → x.extractLsb 3 0 ≠ y.extractLsb 3 0 → False))
  let source ← Smt2Lean.Pipeline.translateSession
    "(set-logic ALL)(push 1)(declare-const x (_ BitVec 4))\
     (define-fun p () Bool (= ((_ sign_extend 4) x) #xff))\
     (check-sat-assuming (p))(pop 1)(declare-const x (_ BitVec 8))\
     (assert (= ((_ extract 3 0) x) #xf))(check-sat)\
     (reset)(set-logic HORN)(declare-fun P ((_ BitVec 12)) Bool)\
     (assert (P ((_ repeat 3) #xf)))(check-sat)" env
  unsafe enableInitializersExecution
  let some emitted ← Elab.runFrontend source
      (({} : Options).setBool `Elab.async false) "Query.lean" `Query
    | throw (IO.userError "width-changing session did not elaborate")
  let check : MetaM Unit := do
    for (name, expected) in #[
      (`Refutation_1, q(∀ x : BitVec 4, x.signExtend 8 = 255 → False)),
      (`Refutation_2, q(∀ x : BitVec 8, x.extractLsb 3 0 = 15 → False)),
      (`Problem_3, q(∃ p : BitVec 12 → Prop, p ((15 : BitVec 4).replicate 3)))
    ] do
      let .defnInfo definition ← getConstInfo name | throwError "missing {name}"
      checkEqual definition.value expected
      checkStatementAxioms name
  discard <| check.toIO { fileName := "width-changing session", fileMap := default } { env := emitted }
  IO.println "Bitvector widths passed: complete SMT/CHC targets and scoped width changes"

/-- Read each destination bit independently of Lean's shift/rotation operations. -/
private def shiftReference (width x amount : Nat) (op : String) : Nat := Id.run do
  let bit (i : Nat) := if i < width then x / 2 ^ i % 2 == 1 else false
  let mut result := 0
  for i in [:width] do
    let on := match op with
      | "bvshl" => amount ≤ i && bit (i - amount)
      | "bvlshr" => bit (i + amount)
      | "bvashr" => if i + amount < width then bit (i + amount) else bit (width - 1)
      | "rotate_left" => bit ((i + width - amount % width) % width)
      | _ => bit ((i + amount) % width)
    if on then result := result + 2 ^ i
  return result

private def checkBitvectorShiftValues (env : Environment) : IO Unit := do
  let mut total := 0
  for width in #[1, 2, 3, 4, 32, 64, 129] do
    let modulus := 2 ^ width
    let values := if width ≤ 4 then (List.range modulus).toArray
      else #[0, 1, modulus / 2 - 1, modulus / 2, modulus / 2 + 1, modulus - 1]
    let amounts := if width ≤ 4 then (List.range modulus).toArray
      else #[0, 1, width - 1, width, width + 1, modulus - 1]
    let literal (n : Nat) := s!"(_ bv{n} {width})"
    let mut rows := #[]
    for x in values do
      let mut checks := #[]
      for amount in amounts do
        for op in #["bvshl", "bvlshr", "bvashr"] do
          checks := checks.push s!"(= ({op} {literal x} {literal amount}) {literal (shiftReference width x amount op)})"
      for amount in #[0, 1, width - 1, width, width + 1, 2 * width + 3, 4294967295] do
        for op in #["rotate_left", "rotate_right"] do
          checks := checks.push s!"(= ((_ {op} {amount}) {literal x}) {literal (shiftReference width x amount op)})"
      total := total + checks.size
      rows := rows.push ("(and " ++ String.intercalate " " checks.toList ++ ")")
    let input := "(set-logic QF_BV)" ++ String.join (rows.toList.map (s!"(assert {·})")) ++ "(check-sat)"
    runQuery env s!"bitvector shifts {width}" input fun query =>
      withAssertions query fun parameters assertions => do
        unless parameters.isEmpty && assertions.size == rows.size do
          throwError "shifts introduced parameters or lost assertions"
        for value in assertions do
          checkWithKernel (← mkDecideProof (← deltaExpand value Smt2Lean.Helpers.isHelper))
  IO.println s!"Bitvector shifts passed: {total} kernel-checked cases; exhaustive widths 1–4 and 32/64/129-bit boundaries"

private def checkBitvectorShifts (env : Environment) : IO Unit := do
  checkBitvectorShiftValues env
  let path := "tests/translation/bitvec/shifts.smt2"
  runQuery env path (← IO.FS.readFile path) fun query => do
    checkFunctionIsolation query
    checkRefutation query (usesClassical := true) q(
      ∀ (x n : BitVec 4) (p : Prop) (f : BitVec 4 → BitVec 4) (named : BitVec 4 → BitVec 4 → BitVec 4),
      (smtShl x n = smtLshr x n ∧
        smtAshr x n = (if BitVec.slt x 0 = true then 15 else 0) ∧
        x.rotateLeft 5 = x.rotateRight 3 ∧
        x.rotateRight 4294967295 = x.rotateRight 3 ∧
        f (smtShl (if p then x else 1) n) = (smtAshr x (smtLshr n 1)).rotateLeft 1 ∧
        smtLshr (smtShl x n) (n.rotateRight 1) = named (smtShl x n) (n.rotateRight 1) ∧
        (∀ x : BitVec 4, ∃ n : BitVec 4, smtShl x n = 0) ∧
        (∀ x n : BitVec 4, smtAshr x n = x.rotateLeft 0)) → False)
  let path := "tests/translation/chc/shifts.smt2"
  runProblem env path (← IO.FS.readFile path) fun problem =>
    checkProblem problem (extraAxioms := #[``propext, ``Quot.sound]) q(
      ∃ (p : BitVec 4 → Prop) (r : BitVec 4 → BitVec 4 → BitVec 4 → Prop),
      p 8 ∧
      (∀ x n : BitVec 4, p x → n < 4 → r (smtShl x n) (smtLshr x n) (smtAshr x n)) ∧
      (∀ x y z : BitVec 4, r x y z → x.rotateLeft 1 = x.rotateRight 3 → p (z.rotateLeft 1)) ∧
      (∀ x : BitVec 4, p x → smtShl x 15 ≠ 0 → False))
  let source ← Smt2Lean.Pipeline.translateSession
    "(set-logic ALL)(declare-const x (_ BitVec 4))(declare-const n (_ BitVec 4))(push 1)\
     (define-fun p () Bool (= (bvshl x n) #x0))(check-sat-assuming (p))(check-sat)(pop 1)\
     (reset)(set-logic ALL)(declare-const x (_ BitVec 8))\
     (assert (= ((_ rotate_right 9) x) #x80))(check-sat)\
     (reset)(set-logic HORN)(declare-fun P ((_ BitVec 1)) Bool)\
     (assert (P (bvashr #b1 #b1)))(check-sat)" env
  unless source.startsWith "import Init" &&
      (source.splitOn "def SMT.bvshl ").length == 2 &&
      (source.splitOn "def SMT.bvashr ").length == 2 && !source.contains "def SMT.bvlshr " do
    throw (IO.userError "shift session emitted the wrong imports/helpers")
  unsafe enableInitializersExecution
  let some emitted ← Elab.runFrontend source
      (({} : Options).setBool `Elab.async false) "Query.lean" `Query
    | throw (IO.userError "shift session did not elaborate")
  let check : MetaM Unit := do
    for (name, expected) in #[
      (`Refutation_1, q(∀ x n : BitVec 4, smtShl x n = 0 → False)),
      (`Refutation_2, q(∀ _x _n : BitVec 4, True → False)),
      (`Refutation_3, q(∀ x : BitVec 8, x.rotateRight 9 = 128 → False)),
      (`Problem_4, q(∃ p : BitVec 1 → Prop, p (smtAshr 1 1)))
    ] do
      let .defnInfo definition ← getConstInfo name | throwError "missing {name}"
      checkEqual (← deltaExpand definition.value Smt2Lean.Helpers.isHelper) expected
      checkStatementAxioms name
  discard <| check.toIO { fileName := "shift session", fileMap := default } { env := emitted }
  IO.println "Shift translation passed: complete SMT/CHC targets, helper names, and four scoped snapshots"

/-- Carrier quantification and nonemptiness are part of the closed statement. -/
private def checkUninterpretedSorts (env : Environment) : IO Unit := do
  let path := "tests/translation/sorts/uninterpreted.smt2"
  runQuery env path (← IO.FS.readFile path) fun query => do
    checkFunctionIsolation query
    checkRefutation query (usesClassical := true) q(
      ∀ A B C : Type, Nonempty A → Nonempty B → Nonempty C →
        ∀ (a b : A) (flag : Prop) (step : A → A) (tag : A → Prop → Int → B) (P : B → Prop),
          ((if flag then a else b) = (if flag then a else b) ∧
            (a ≠ b ∧ a ≠ step a ∧ b ≠ step a) ∧
            (∀ x : A, ∃ y : A, y = step x) ∧
            (∀ _a : A, a = b) ∧
            (∀ x : A, x = a → tag x flag 0 = tag a flag 0) ∧
            P (tag (if flag then a else b) flag 1) ∧
            P (tag (if flag then a else b) flag 1)) → False)
  let path := "tests/translation/chc/uninterpreted.smt2"
  runProblem env path (← IO.FS.readFile path) fun problem =>
    checkProblem problem (usesClassical := true) q(
      ∃ A : Type, Nonempty A ∧ ∃ B : Type, Nonempty B ∧
        ∃ (reach : A → Prop) (edge : A → B → Prop → Int → Prop) (_unused : B → Prop),
          (∀ x : A, reach x) ∧
          (∀ (x y : A) (l : B) (b : Prop) (i : Int),
            reach x → x = y → b → i > 0 → edge (if b then x else y) l b i) ∧
          (∀ (x y : A) (l : B) (b : Prop) (i : Int), edge x l b i → x ≠ y → reach y) ∧
          (∀ x y : A, reach x → reach y → x ≠ y → False))
  for logic in #["QF_UF", "UF", "ALL"] do
    runQuery env "unused sort" s!"(set-logic {logic})(declare-sort S 0)(check-sat)"
      fun query => checkRefutation query q(∀ A : Type, Nonempty A → True → False)
  runProblem env "unused CHC sort" "(set-logic HORN)(declare-sort S 0)(check-sat)"
    fun problem => checkProblem problem q(∃ A : Type, Nonempty A ∧ True)
  runQuery env "nonempty carrier"
    "(set-logic UF)(declare-sort S 0)(assert (forall ((x S)) false))(check-sat)"
    fun query => checkRefutation query q(∀ A : Type, Nonempty A → (∀ _x : A, False) → False)
  runProblem env "nonempty CHC carrier"
    "(set-logic HORN)(declare-sort S 0)(assert (forall ((x S)) false))(check-sat)"
    fun problem => checkProblem problem q(∃ A : Type, Nonempty A ∧ (∀ _x : A, False))
  IO.println "Uninterpreted sorts passed: arbitrary nonempty carriers, SMT/CHC closure, aliases, and mixed functions"

private def checkSessions (env : Environment) : IO Unit := do
  let base := q(∀ p : Prop, p → False)
  let integer := q(∀ (p : Prop) (x : Int), (p ∧ x + 1 > 0) → False)
  let conditional := q(∀ (p : Prop) (x : Int), (p ∧ (if p then x else -x) = x) → False)
  let fact := q(∃ p : Int → Prop, p 0)
  let cases : Array (String × String × Array Expr × Array Nat) := #[
    ("smt", "Refutation", #[base, integer,
      q(∀ (p : Prop) (x : Int) (q : Prop),
        (p ∧ x + 1 > 0 ∧ (q ∧ exclusive p q ∧ (x ≠ 0 ∧ x ≠ x + 1 ∧ 0 ≠ x + 1))) → False),
      integer, base,
      q(∀ p x : Prop, (p ∧ ¬x ∧ (¬x ∨ exclusive p x)) → False),
      conditional, conditional], #[7, 8]),
    ("sorts", "Refutation", #[
      q(∀ A : Type, Nonempty A → ∀ x : A, x = x → False),
      q(∀ A B : Type, Nonempty A → Nonempty B → ∀ (x : A) (y : B), (x = x ∧ y = y) → False),
      q(∀ A : Type, Nonempty A → ∀ x : A, x = x → False),
      q(∀ A B : Type, Nonempty A → Nonempty B → ∀ (x : A) (p : B → Prop),
        (x = x ∧ ∀ y : B, p y) → False),
      q(∀ A : Type, Nonempty A → (∀ _x : A, False) → False),
      q(∀ A : Type, Nonempty A → (∀ x : A, x = x) → False),
      q(∀ A : Type, Nonempty A → (∀ x : A, x = x) → False), q(True → False)], #[]),
    ("resets", "Refutation", #[
      q(∀ (p : Prop) (x : Int), (p ∧ x + 1 > 0 ∧ p) → False), q(True → False),
      q(∀ p : Int, p = 1 → False), q(∀ p : Prop, ¬p → False),
      q(∀ _p : Prop, True → False), q(∀ (p : Prop) (_x : Int), ¬p → False), q(True → False)], #[]),
    ("assuming", "Refutation", #[q(∀ p : Prop, (p ∧ ¬p) → False), base, base,
      q(∀ p : Prop, (p ∧ p ∧ p ∧ p) → False),
      q(∀ p q : Prop, (p ∧ q ∧ ¬p) → False), q(∀ (p : Prop) (_q : Int), p → False)], #[]),
    ("chc", "Problem", #[fact,
      q(∃ (p : Int → Prop) (r : Int → Prop → Prop),
        p 0 ∧ (∀ x : Int, p x → x > 0 → r (x + 1) True)),
      q(∃ (p : Int → Prop) (r : Int → Prop → Prop) (done : Prop),
        p 0 ∧ (∀ x : Int, p x → x > 0 → r (x + 1) True) ∧
          (∀ x : Int, r x True → done)),
      fact,
      q(∃ (p : Int → Prop) (r : Prop → Prop), p 0 ∧ (∀ b : Prop, b → r b)),
      fact], #[])
  ]
  for (fixture, baseName, expected, classicalQueries) in cases do
    let path := s!"tests/translation/sessions/{fixture}.smt2"
    let source ← Smt2Lean.Pipeline.translateSession (← IO.FS.readFile path) env path
    let [statements, proofs] := source.splitOn "-- Proofs\n"
      | throw (IO.userError "wrong session layout")
    unless !statements.contains "sorry" && !proofs.contains "def " &&
        (statements.splitOn s!"def {baseName}_").length == expected.size + 1 &&
        (proofs.splitOn "theorem ").length == expected.size + 1 do
      throw (IO.userError "wrong session statement/proof count")
    if fixture == "smt" then
      for helper in #["SMT.xor", "SMT.distinct3"] do
        unless (statements.splitOn s!"def {helper}").length == 2 do
          throw (IO.userError "session helpers must be emitted once")
    unsafe enableInitializersExecution
    let some emitted ← Elab.runFrontend source
        (({} : Options).setBool `Elab.async false) "Query.lean" `Query
      | throw (IO.userError "session did not elaborate")
    let check : MetaM Unit := do
      for i in [:expected.size] do
        let name := Name.mkSimple s!"{baseName}_{i + 1}"
        let proofName := Name.mkSimple s!"{baseName.toLower}_{i + 1}"
        let .defnInfo definition ← getConstInfo name | throwError "missing {name}"
        if definition.value.hasFVar || definition.value.hasMVar || definition.value.hasLooseBVars then
          throwError "{name} contains unresolved variables"
        checkEqual definition.type q(Prop)
        let value ← deltaExpand definition.value Smt2Lean.Helpers.isHelper
        checkEqual value expected[i]!
        checkAxioms name (classicalQueries.contains (i + 1))
        let .thmInfo proof ← getConstInfo proofName | throwError "missing {proofName}"
        unless proof.type == mkConst name do throwError "wrong proof target for {name}"
        let axioms ← collectAxioms proofName
        let statementAxioms ← collectAxioms name
        unless axioms.contains ``sorryAx && axioms.size == statementAxioms.size + 1 &&
            statementAxioms.all axioms.contains do
          throwError "unexpected proof axioms for {name}"
        unless statements.contains s!"(query {i + 1}: check-sat" do
          throwError "missing query source for {name}"
    discard <| check.toIO { fileName := path, fileMap := default } { env := emitted }
  let source ← Smt2Lean.Pipeline.translateSession
    "(set-logic ALL)(check-sat)(push 1)(assert (= (div 1 0) 7))(check-sat)\
     (push 1)(assert (= (mod 1 0) 3))(check-sat)(pop 2)(check-sat)\
     (reset)(set-logic HORN)(assert (=> (= (div 1 0) 7) false))(check-sat)" env
  unsafe enableInitializersExecution
  let some emitted ← Elab.runFrontend source
      (({} : Options).setBool `Elab.async false) "Query.lean" `Query
    | throw (IO.userError "division session did not elaborate")
  let check : MetaM Unit := do
    for (name, expected) in #[
      (`Refutation_1, q(True → False)),
      (`Refutation_2, q(∀ d : Int → Int, smtDiv d 1 0 = 7 → False)),
      (`Refutation_3, q(∀ d m : Int → Int, (smtDiv d 1 0 = 7 ∧ smtMod m 1 0 = 3) → False)),
      (`Refutation_4, q(True → False)),
      (`Problem_5, q(∃ d : Int → Int, smtDiv d 1 0 = 7 → False))
    ] do
      let .defnInfo definition ← getConstInfo name | throwError "missing {name}"
      checkEqual (← deltaExpand definition.value Smt2Lean.Helpers.isHelper) expected
      checkStatementAxioms name
  discard <| check.toIO { fileName := "division session", fileMap := default } { env := emitted }
  IO.println "Session translation passed: SMT/CHC goals match handwritten propositions"

def main : IO Unit := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules #[{ module := `Smt2Lean.Translate }] {} (loadExts := true)
  checkSessions env
  checkUninterpretedSorts env
  checkAxiomRejection
  checkOperatorSemantics env
  checkDivision env
  checkReals env
  checkConversions env
  checkBitvectors env
  checkBitvectorWidths env
  checkBitvectorShifts env
  checkLetBindings env
  checkDefinitions env
  checkNamedAssertions env
  checkQuantifierHints env
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
  let configured ← IO.FS.readFile "tests/translation/bool/options.smt2"
  for status in #["", "sat", "unsat", "unknown"] do
    let metadata := if status.isEmpty then "" else s!"(set-info :status {status})\n"
    for input in #[metadata ++ contradiction, configured.replace "(set-info :status unknown)" metadata] do
      runQuery env s!"contradiction ({status})" input fun query =>
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
  IO.println "Translation passed: 33 refutations and emitted definitions; types and axiom dependencies checked"
