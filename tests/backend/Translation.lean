import tests.backend.Arithmetic
import tests.backend.BitVec
import tests.backend.Sessions
import tests.backend.Datatypes
import tests.backend.Sharing

open Lean Meta Qq Classical
open Smt2Lean.Tests
open Smt2Lean.Backend Smt2Lean.Translate Smt2Lean.Emit

local notation "exclusive" => (fun p q : Prop => (p ∧ ¬q) ∨ (¬p ∧ q))

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

/-- Check source structure as well as the kernel-checked expanded reference. -/
private def checkSourceBindings (env : Environment) : IO Unit := do
  let path := "tests/translation/bindings/preserved.smt2"
  runQuery env path (← IO.FS.readFile path) fun query => do
    let statement ← refutationStatement query
    unless statement.definitions.map (·.name) == #[`Refutation.Definitions.inc, `Refutation.Definitions.twice] do
      throwError "lost source definitions or dependency order"
    let text ← render statement.value (parts := statement.parts) (definitions := statement.definitions)
    for fragment in #["Refutation.Definitions.inc (Refutation.Definitions.inc n)",
        "let next := Refutation.Definitions.twice", "let old :=", "let next := Refutation.Definitions.inc"] do
      unless text.contains fragment do throwError "source structure missing: {fragment}"
    checkEmission statement.value (parts := statement.parts) (definitions := statement.definitions)
    let rejected ← try
      discard <| Smt2Lean.Equivalence.prove q(True) q(False) (fun _ => false)
      pure false
    catch _ => pure true
    unless rejected do throwError "equivalence check accepted different propositions"
  runQuery env "source-bindings-theories" "
    (set-logic ALL)
    (declare-datatype D ((zero) (pair (left Int) (right Int))))
    (declare-const |smt2lean.let.0.0| Int)
    (define-fun choose ((b Bool) (n Int)) Int (ite b n 0))
    (define-fun get ((d D) (n Int)) Int
      (let ((saved n)) (match d ((zero saved) ((pair n y) (+ saved n y))))))
    (define-fun bump ((b (_ BitVec 8))) (_ BitVec 8) (bvadd b #x01))
    (define-fun shift ((r Real)) Real (+ r 0.5))
    (define-fun lookup ((a (Array Int Int)) (i Int)) Int (select a i))
    (assert (= (get (pair 1 2) 3) 6))
    (assert (= (choose false 7) 0))
    (assert (= (let ((b (bump #x02))) b) #x03))
    (assert (= (let ((r (shift 1.5))) r) 2.0))
    (assert (= (let ((a ((as const (Array Int Int)) 5))) (lookup a 0)) 5))
    (check-sat)" fun query => do
      unless query.declarations.size == 1 do throwError "private let markers escaped into parameters"
      let statement ← refutationStatement query
      unless statement.definitions.size == 5 do throwError "missing theory definitions"
      checkEmission statement.value (parts := statement.parts) (definitions := statement.definitions)
  -- An inner conditional changes the outer condition's hidden Decidable type.
  runProblem env "source-bindings-nested-conditionals" "
    (set-logic HORN)(declare-fun R (Int) Bool)
    (define-fun valid ((n Int)) Bool (and (>= n 0) (< n 10)))
    (define-fun read ((n Int)) Int (ite (valid n) (+ n 1) 0))
    (assert (forall ((n Int)) (=> (R n) (R (read (read n))))))
    (check-sat)" fun problem => do
      let step : Q(Int → Int) := q(fun n => if n ≥ 0 ∧ n < 10 then n + 1 else 0)
      checkProblem problem (usesClassical := true) q(∃ r : Int → Prop, ∀ n : Int, r n → r ($step ($step n)))
  runProblem env "source-bindings-horn" "
    (set-logic HORN)(declare-fun R (Int) Bool)
    (define-fun inc ((n Int)) Int (+ n 1))
    (define-fun positive ((n Int)) Bool (> n 0))
    (assert (R 0))
    (assert (forall ((x Int)) (let ((next (inc x)))
      (=> (and (R x) (positive next)) (R next)))))
    (check-sat)" fun problem => do
      let statement ← problemStatement problem
      let text ← render statement.value .problem (parts := statement.parts) (definitions := statement.definitions)
      for fragment in #["let next := Problem.Definitions.inc", "Problem.Definitions.positive next", "r0 next"] do
        unless text.contains fragment do throwError "Horn source structure missing: {fragment}"
      checkEmission statement.value .problem (parts := statement.parts) (definitions := statement.definitions)
  IO.println "Source preservation passed: named calls, lets, match scopes, mixed theories, and Horn clauses"

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

private def checkHornProblems (env : Environment) : IO Unit := do
  runProblem env "background-symbol-witnesses" "
    (set-logic HORN)(declare-const c Int)(declare-fun f (Int) Int)(declare-fun P (Int) Bool)
    (assert (= (f c) c))
    (assert (P (f c)))
    (assert (forall ((x Int)) (=> (and (P x) (< x (f c))) false)))
    (check-sat)" fun problem => do
      checkProblem problem q(∃ (c : Int) (f : Int → Int) (p : Int → Prop),
        (¬(f c = c) → False) ∧ p (f c) ∧ (∀ x : Int, p x → x < f c → False))
      let clauses := mkConst `Problem.Clauses
      checkEqual (← inferType clauses) q(Int → (Int → Int) → (Int → Prop) → Prop)
      checkEqual (mkAppN clauses #[q((0 : Int)), q(fun x : Int => x), q(fun x : Int => x = 0)])
        q((¬((0 : Int) = 0) → False) ∧ (0 : Int) = 0 ∧ (∀ x : Int, x = 0 → x < 0 → False))
  let surface := "tests/translation/chc/surface-forms.smt2"
  runProblem env surface (← IO.FS.readFile surface) fun problem =>
    checkProblem problem q(∃ (p q : Int → Prop) (done : Prop),
      (∀ x : Int, p x → x > 0 → q x) ∧
      (∀ x : Int, p x → ¬(x < 0) → q x) ∧
      (∀ x : Int, p x → x > 0 → q x) ∧
      p 0 ∧
      (∀ x : Int, p x → q x) ∧
      (∀ x : Int, q x → ¬(x ≥ 0) → False) ∧
      (∀ outer inner : Int, p outer → q inner) ∧
      (∀ outer inner : Int, q inner → ¬(outer = inner) → False) ∧
      (∀ x : Int, ¬(x < 0) → ¬(x ≥ 0) → False) ∧
      (done → ¬True → False) ∧
      (done → False) ∧
      (∀ x : Int, p x → q x → False) ∧
      (∀ x : Int, ¬(x = x) → False))
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

private def checkCore (env : Environment) : IO Unit := do
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

private def checkNamedClauses (env : Environment) : IO Unit := do
  let premises := String.intercalate " " (List.replicate 100 "(R x)")
  let input := "(set-logic HORN)(declare-sort S 0)(declare-fun R (S) Bool)" ++
    "(declare-fun unused (Int) Bool)(assert (forall ((x S)) (R x)))" ++
    s!"(assert (forall ((x S)) (=> (and {premises}) (R x))))(check-sat)"
  runProblem env "long clause" input fun problem => do
    let original ← defineProblem problem `Original
    let statement ← problemStatement problem
    checkEqual statement.value original
    unless statement.parts.size == 3 &&
        statement.parts[2]?.map (·.name) == some `Problem.Clauses do
      throwError "lost clause boundaries or the parameterized Clauses definition"
    for part in statement.parts.pop do
      lambdaTelescope part.value fun parameters _ => do
        unless parameters.size == 2 do
          throwError "a clause must bind its carrier and relation, but not the unused relation"
    checkEmission statement.value .problem problem.source
      (problem.clauses.filterMap (·.source)) statement.parts statement.definitions
    let source ← render statement.value .problem (parts := statement.parts)
    for line in source.splitOn "\n" do
      if (line.toList.takeWhile (· == ' ')).length > 12 then
        throwError "logical-chain indentation grew with the number of premises"
  IO.println "Named clauses passed: dependent parameters, unused relations, 100 premises, and emitted equivalence"

/-- Bound the lifetime of imported/elaborated environments across the full suite. -/
def main (args : List String) : IO Unit := do
  if let ["--emission", path] := args then
    initSearchPath (← findSysroot)
    unsafe enableInitializersExecution
    let env ← importModules #[{ module := `Smt2Lean.Translate }] {} (loadExts := true)
    let input ← IO.FS.readFile path
    (Smt2Lean.Chc.parseAndInspectProblem input (name := path) fun problem => do
      let action : MetaM Unit := do
        let statement ← problemStatement problem
        checkEmission statement.value .problem problem.source
          (problem.clauses.filterMap (·.source)) statement.parts statement.definitions
      discard <| action.toIO
        { fileName := path, fileMap := default, maxRecDepth := 4096,
          options := Lean.maxRecDepth.set {} 4096 } { env }
    ).runIO
    IO.println "Emission equivalence passed: named clauses, printed definitions, and assembled Problem"
    return
  let groups : Array (String × (Environment → IO Unit)) := #[
    ("scopes", fun env => do
      checkSharing env
      checkDatatypes env
      checkSessions env
      checkUninterpretedSorts env),
    ("arithmetic", fun env => do
      checkAxiomRejection
      checkOperatorSemantics env
      checkDivision env
      checkReals env
      checkConversions env),
    ("bitvectors", fun env => do
      checkBitvectors env
      checkBitvectorWidths env
      checkBitvectorShifts env
      checkBitvectorDivision env
      checkBitvectorConversions env),
    ("bindings", fun env => do
      checkLetBindings env
      checkDefinitions env
      checkSourceBindings env
      checkNamedAssertions env
      checkQuantifierHints env),
    ("horn", fun env => do
      checkNamedClauses env
      checkHornReconstruction env
      checkHornProblems env),
    ("core", checkCore)]
  if args.isEmpty then
    for (name, _) in groups do
      let child ← IO.Process.spawn { cmd := (← IO.appPath).toString, args := #[name] }
      let code ← child.wait
      unless code == 0 do throw (IO.userError s!"translation group '{name}' failed ({code})")
  else
    let [name] := args | throw (IO.userError "expected one translation group name")
    let some (_, run) := groups.find? (·.1 == name)
      | throw (IO.userError s!"unknown translation group: {name}")
    initSearchPath (← findSysroot)
    unsafe enableInitializersExecution
    let env ← importModules #[{ module := `Smt2Lean.Translate }] {} (loadExts := true)
    run env
