import tests.backend.Support

open Lean Meta Qq Classical
open Smt2Lean.Backend Smt2Lean.Translate Smt2Lean.Emit

open Smt2Lean.Tests

namespace Smt2Lean.Tests

local notation "smtDiv" => (fun (zero : Int → Int) (x y : Int) => ite (y = 0) (zero x) (x / y))
local notation "smtShl" => (fun {w : Nat} (x y : BitVec w) => x <<< min (BitVec.toNat y) w)
local notation "smtLshr" => (fun {w : Nat} (x y : BitVec w) => x >>> min (BitVec.toNat y) w)
local notation "smtAshr" => (fun {w : Nat} (x y : BitVec w) => BitVec.sshiftRight x (min (BitVec.toNat y) w))

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

def checkBitvectors (env : Environment) : IO Unit := do
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

def checkBitvectorWidths (env : Environment) : IO Unit := do
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

def checkBitvectorShifts (env : Environment) : IO Unit := do
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

/-- Independent integer arithmetic oracle, including all zero-divisor cases. -/
private def checkBitvectorDivisionValues (env : Environment) : IO Unit := do
  let mut total := 0
  for width in #[1, 2, 3, 4, 32, 64, 129] do
    let modulus := 2 ^ width
    let half := modulus / 2
    let values := if width ≤ 4 then (List.range modulus).toArray
      else #[0, 1, half - 1, half, half + 1, modulus - 1]
    let literal (n : Nat) := s!"(_ bv{n} {width})"
    let signed (n : Nat) : Int := if n < half then (n : Int) else (n : Int) - modulus
    let wrap (n : Int) := (n % (modulus : Int)).toNat
    let mut rows := #[]
    for x in values do
      for y in values do
        let a := signed x
        let b := signed y
        let magnitude : Int := a.natAbs / b.natAbs
        let quotient := if (a < 0) != (b < 0) then -magnitude else magnitude
        let remainder := if y == 0 then a else a - quotient * b
        let modulo := if remainder != 0 && (remainder < 0) != (b < 0) then remainder + b else remainder
        let results := #[
          ("bvudiv", if y == 0 then modulus - 1 else x / y),
          ("bvurem", if y == 0 then x else x % y),
          ("bvsdiv", if y == 0 then (if a < 0 then 1 else modulus - 1) else wrap quotient),
          ("bvsrem", wrap remainder), ("bvsmod", wrap modulo)]
        let checks := results.map fun (op, expected) =>
          s!"(= ({op} {literal x} {literal y}) {literal expected})"
        rows := rows.push ("(and " ++ String.intercalate " " checks.toList ++ ")")
        total := total + checks.size
    let input := "(set-logic QF_BV)" ++ String.join (rows.toList.map (s!"(assert {·})")) ++ "(check-sat)"
    runQuery env s!"bitvector division {width}" input fun query =>
      withAssertions query fun parameters assertions => do
        unless parameters.isEmpty && assertions.size == rows.size do
          throwError "BV division introduced parameters or lost assertions"
        for value in assertions do checkWithKernel (← mkDecideProof value)
  IO.println s!"Bitvector division passed: {total} kernel-checked cases; exhaustive widths 1–4 and 32/64/129-bit boundaries"

def checkBitvectorDivision (env : Environment) : IO Unit := do
  checkBitvectorDivisionValues env
  let path := "tests/translation/bitvec/division.smt2"
  runQuery env path (← IO.FS.readFile path) fun query => do
    checkFunctionIsolation query
    checkRefutation query (usesClassical := true) q(
      ∀ (x y : BitVec 4) (p : Prop) (f : BitVec 4 → BitVec 4) (named : BitVec 4 → BitVec 4 → BitVec 4),
      (BitVec.smtUDiv x y = f x ∧ x % y = BitVec.srem x y ∧
        BitVec.smtSDiv (if p then x else y) y = BitVec.smod x y ∧
        BitVec.smod (BitVec.smtSDiv x y) (x % y) = named (BitVec.smtSDiv x y) (x % y) ∧
        (∀ x : BitVec 4, ∃ y : BitVec 4, BitVec.smtUDiv x y = x) ∧
        (∀ x y : BitVec 4, BitVec.srem x y = x % y)) → False)
  let path := "tests/translation/chc/bv-division.smt2"
  runProblem env path (← IO.FS.readFile path) fun problem =>
    checkProblem problem (extraAxioms := #[``propext]) q(
      ∃ (p : BitVec 4 → Prop) (r : BitVec 4 → BitVec 4 → BitVec 4 → Prop),
      p 8 ∧
      (∀ x y : BitVec 4, p x → r (BitVec.smtUDiv x y) (x % y) (BitVec.smtSDiv x y)) ∧
      (∀ x y z : BitVec 4, r x y z → BitVec.srem x y = 0 → p (BitVec.smod z y)) ∧
      (∀ x : BitVec 4, p x → x % 0 ≠ x → False))
  IO.println "BV division translation passed: complete SMT/CHC targets, symbolic operands, and binding scope"

/-- Compare conversions and overflow flags with unbounded integer arithmetic. -/
private def checkBitvectorConversionValues (env : Environment) : IO Unit := do
  let mut total := 0
  for width in #[1, 2, 3, 4, 32, 64, 129] do
    let modulus := 2 ^ width
    let half := modulus / 2
    let values := if width ≤ 4 then (List.range modulus).toArray
      else #[0, 1, half - 1, half, half + 1, modulus - 1]
    let literal (n : Nat) := s!"(_ bv{n} {width})"
    let integer (n : Int) := if n < 0 then s!"(- {n.natAbs})" else toString n
    let signed (n : Nat) : Int := if n < half then (n : Int) else (n : Int) - modulus
    let overflow (n : Int) := decide (n < -(half : Int) ∨ (half : Int) ≤ n)
    let test (term : String) (truth : Bool) := if truth then term else s!"(not {term})"
    let inputs : Array Int := if width ≤ 4 then
        (List.range (4 * modulus + 1)).toArray.map (fun (n : Nat) => (n : Int) - 2 * modulus)
      else #[0, 1, -1, (half : Int) - 1, half, -(half : Int), -(half : Int) - 1,
        (modulus : Int) - 1, modulus, (modulus : Int) + 1, -(modulus : Int),
        -(modulus : Int) - 1, (modulus : Int) ^ 2 + 1, -(modulus : Int) ^ 2 - 1]
    let mut rows : Array (Array String) := #[]
    for n in inputs do
      let residue := (n % (modulus : Int)).toNat
      let cast := s!"((_ int_to_bv {width}) {integer n})"
      rows := rows.push #[s!"(= {cast} {literal residue})",
        s!"(= ((_ int2bv {width}) {integer n}) {literal residue})",
        s!"(= (ubv_to_int {cast}) {residue})", s!"(= (sbv_to_int {cast}) {integer (signed residue)})"]
    for x in values do
      let a := literal x
      rows := rows.push #[s!"(= (ubv_to_int {a}) {x})", s!"(= (bv2nat {a}) {x})",
        s!"(= (sbv_to_int {a}) {integer (signed x)})",
        s!"(= ((_ int_to_bv {width}) (ubv_to_int {a})) {a})",
        s!"(= ((_ int_to_bv {width}) (sbv_to_int {a})) {a})",
        test s!"(bvnego {a})" (overflow (-signed x))]
      for y in values do
        let b := literal y
        rows := rows.push #[test s!"(bvuaddo {a} {b})" (x + y ≥ modulus),
          test s!"(bvsaddo {a} {b})" (overflow (signed x + signed y)),
          test s!"(bvumulo {a} {b})" (x * y ≥ modulus),
          test s!"(bvsmulo {a} {b})" (overflow (signed x * signed y))]
    let input := "(set-logic ALL)" ++ String.join (rows.toList.map fun checks =>
      "(assert (and " ++ String.intercalate " " checks.toList ++ "))") ++ "(check-sat)"
    total := total + rows.foldl (fun n checks => n + checks.size) 0
    runQuery env s!"bitvector conversions {width}" input fun query =>
      withAssertions query fun parameters assertions => do
        unless parameters.isEmpty && assertions.size == rows.size do
          throwError "BV conversions introduced parameters or lost assertions"
        for value in assertions do checkWithKernel (← mkDecideProof value)
  IO.println s!"BV conversions passed: {total} kernel-checked cases; exhaustive widths 1–4 and 32/64/129-bit boundaries"

def checkBitvectorConversions (env : Environment) : IO Unit := do
  checkBitvectorConversionValues env
  let path := "tests/translation/bitvec/conversions.smt2"
  runQuery env path (← IO.FS.readFile path) fun query => do
    checkFunctionIsolation query
    checkRefutation query (usesClassical := true) q(
      ∀ (n : Int) (x y : BitVec 8) (p : Prop) (f : BitVec 8 → Int → Prop → BitVec 8) (named : Int → BitVec 8),
      (BitVec.ofInt 8 n = BitVec.ofInt 8 n ∧ (x.toNat : Int) = (x.toNat : Int) ∧
        x.toInt = (x.toNat : Int) - 256 ∧
        (x.negOverflow = true ∧ x.uaddOverflow y = true ∧ ¬x.saddOverflow y = true ∧
          x.umulOverflow y = true ∧ x.smulOverflow y = true) ∧
        f (if p then BitVec.ofInt 8 n else x) y.toInt (x.uaddOverflow y = true) = named n ∧
        BitVec.ofInt 8 x.toInt = BitVec.ofInt 8 n ∧
        (∀ n : Int, ∃ x : BitVec 8, x.toInt = (BitVec.ofInt 8 n).toInt)) → False)
  let path := "tests/translation/chc/bv-conversions.smt2"
  runProblem env path (← IO.FS.readFile path) fun problem =>
    checkProblem problem (extraAxioms := #[``propext]) q(
      ∃ (p : BitVec 8 → Prop) (r : Int → Int → Prop → Prop),
      p (BitVec.ofInt 8 (-1)) ∧
      (∀ x y : BitVec 8, p x → x.uaddOverflow y = true → (¬x.saddOverflow y = true) →
        r (x.toNat : Int) y.toInt (x.negOverflow = true)) ∧
      (∀ (n m : Int) (b : Prop), r n m b → (BitVec.ofInt 8 n).umulOverflow (BitVec.ofInt 8 m) = true →
        p (BitVec.ofInt 8 (n + m))) ∧
      (∀ x y : BitVec 8, p x → x.smulOverflow y = true → False))
  runQuery env "BV conversions with Real and arbitrary Int division"
    "(set-logic ALL)(declare-const n Int)(declare-const r Real)(declare-const x (_ BitVec 8))\
     (assert (= ((_ int_to_bv 8) (div n 0)) x))\
     (assert (= (to_real (ubv_to_int x)) r))\
     (assert (= ((_ int_to_bv 8) (to_int r)) x))(check-sat)"
    fun query => checkRefutation query (usesClassical := true) q(
      ∀ (d : Int → Int) (n : Int) (r : Real) (x : BitVec 8),
      (BitVec.ofInt 8 (smtDiv d n 0) = x ∧ ((x.toNat : Int) : Real) = r ∧
        BitVec.ofInt 8 (Int.floor r) = x) → False)
  let source ← Smt2Lean.Pipeline.translateSession
    "(set-logic ALL)(declare-const x Int)(push 1)\
     (define-fun p () Bool (= ((_ int_to_bv 4) x) #xf))(check-sat-assuming (p))(check-sat)(pop 1)\
     (reset)(set-logic ALL)(declare-const x (_ BitVec 8))\
     (assert (= (sbv_to_int x) (- 1)))(check-sat)\
     (reset)(set-logic HORN)(declare-fun P (Int) Bool)(assert (P (ubv_to_int #x80)))(check-sat)" env
  unless source.startsWith "import Init" && !source.contains "def SMT." do
    throw (IO.userError "conversion session added unexpected imports or helpers")
  unsafe enableInitializersExecution
  let some emitted ← Elab.runFrontend source
      (({} : Options).setBool `Elab.async false) "Query.lean" `Query
    | throw (IO.userError "conversion session did not elaborate")
  let check : MetaM Unit := do
    for (name, expected) in #[
      (`Refutation_1, q(∀ x : Int, BitVec.ofInt 4 x = 15 → False)),
      (`Refutation_2, q(∀ _x : Int, True → False)),
      (`Refutation_3, q(∀ x : BitVec 8, x.toInt = -1 → False)),
      (`Problem_4, q(∃ p : Int → Prop, p ((128 : BitVec 8).toNat : Int)))
    ] do
      let .defnInfo definition ← getConstInfo name | throwError "missing {name}"
      checkEqual definition.value expected
      checkStatementAxioms name
  discard <| check.toIO { fileName := "BV conversion session", fileMap := default } { env := emitted }
  IO.println "BV conversion translation passed: complete SMT/CHC targets, aliases, overflow guards, and four scoped snapshots"

end Smt2Lean.Tests
