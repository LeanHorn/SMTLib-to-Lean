import tests.backend.Support

open Lean Meta Qq Classical
open Smt2Lean.Backend Smt2Lean.Translate Smt2Lean.Emit

open Smt2Lean.Tests

namespace Smt2Lean.Tests

local notation "smtDiv" => (fun (zero : Int → Int) (x y : Int) => ite (y = 0) (zero x) (x / y))
local notation "smtRealDiv" => (fun (zero : Real → Real) (x y : Real) => ite (y = 0) (zero x) (x / y))
local notation "smtMod" => (fun (zero : Int → Int) (x y : Int) => ite (y = 0) (zero x) (x % y))

/-- Compare signed arithmetic with a quotient/remainder search using only +, *, and order. -/
def checkDivision (env : Environment) : IO Unit := do
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
def checkReals (env : Environment) : IO Unit := do
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
def checkConversions (env : Environment) : IO Unit := do
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

end Smt2Lean.Tests
