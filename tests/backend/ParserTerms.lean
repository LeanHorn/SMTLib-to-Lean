import tests.backend.ParserSupport

namespace Smt2Lean.Tests.Parser

open Smt2Lean.Backend

def checkSorts : IO Unit := do
  let expected := #[(1, 1), (2, 2), (1, 1), (2, 2), (1, 0), (1, 0), (1, 0), (0, 0)]
  let identities ← IO.mkRef (#[] : Array (Array UInt64))
  (parseAndInspectSession (← IO.FS.readFile "tests/translation/sessions/sorts.smt2") fun query => do
    require ((query.sorts.size, query.declarations.size) == expected[query.number - 1]!)
      "incorrect sort/declaration lifetimes"
    identities.modify (·.push (query.sorts.map (fun s => hash s.sort)))
    for sort in query.sorts do
      require (sort.source.isSome && sort.sort.isUninterpretedSort) "missing sort identity or source"
    require (!(query.invoked.any (·.startsWith "check-sat"))) "solver query invoked"
  ).runIO
  let ids ← identities.get
  require (ids.size == 8 && ids[0]! == ids[2]! && ids[1]![1]! != ids[3]![1]! &&
      ids[0]! != ids[4]! && ids[4]! != ids[5]! && ids[5]! == ids[6]!)
    "sort identity did not follow declaration scopes"
  for (name, body, ordinal, reason) in #[
    ("sort-arity", "(declare-sort S 1)", 2, "only arity 0"),
    ("sort-mismatch", "(declare-sort S 0)(declare-sort T 0)(declare-const s S)(declare-const t T)(assert (= s t))",
      6, "type"),
    ("sort-after-check", "(check-sat)(declare-sort S 0)", 3, "after check-sat"),
    ("sort-alias-hidden-string", "(declare-sort S 0)(define-sort Bad (T) String)", 3, "unsupported sort alias")
  ] do
    checkRejected name ("(set-logic ALL)" ++ body ++ "(check-sat)") ordinal reason
  for body in #[
    "(push 1)(declare-sort S 0)(pop 1)(declare-const x S)",
    "(declare-sort S 0)(reset-assertions)(declare-const x S)",
    "(declare-sort S 0)(define-sort Alias () S)(reset-assertions)(declare-const x Alias)",
    "(declare-sort S 0)(reset)(set-logic ALL)(declare-const x S)",
    "(declare-sort S 0)(set-option :global-declarations true)"
  ] do
    match ← (parseAndInspectSession ("(set-logic ALL)" ++ body ++ "(check-sat)") (fun _ => pure ())).run with
    | .ok _ => throw (IO.userError s!"accepted invalid sort lifetime: {body}")
    | .error _ => pure ()
  IO.println "Sort parsing passed: native identity, aliases, local/global scopes, and resets"

def checkDivision : IO Unit := do
  let path := "tests/translation/int/division.smt2"
  (parseAndInspectQuery (← IO.FS.readFile path) (name := path) fun query => do
    require (query.assertionTerms.size == 11 && query.definitions.size == 2) "division fixture lost terms"
    require (!(query.invoked.any (·.startsWith "check-sat"))) "division invoked a solver query"
  ).runIO
  for term in #["(div 1)", "(mod 1)", "(mod 1 2 3)", "(div true 2)", "(mod 1 false)", "(div 1.5 2)"] do
    match ← (parseAndInspectQuery s!"(set-logic ALL)(assert (= {term} 0))(check-sat)" (fun _ => pure ())).run with
    | .ok _ => throw (IO.userError s!"accepted ill-typed division: {term}")
    | .error _ => pure ()

def checkReals : IO Unit := do
  checkAccepted "closed-real-comparison"
    "(set-logic ALL)(assert (< 1.0 2.0))(check-sat)" #[] 1 #["set-logic", "assert"]
  let path := "tests/translation/real/arithmetic.smt2"
  (parseAndInspectQuery (← IO.FS.readFile path) (name := path) fun query => do
    require (query.assertionTerms.size == 12 && query.definitions.size == 2) "Real fixture lost terms"
    let some declaration := query.declarations[0]? | throw (.error "missing Real declaration")
    require declaration.term.getSort!.isReal "Real alias lost its sort"
    require (!(query.invoked.any (·.startsWith "check-sat"))) "Real query invoked a solver"
  ).runIO
  for logic in #["QF_LRA", "QF_NRA", "QF_UFLRA", "QF_UFNRA", "LRA", "NRA", "UFLRA", "UFNRA"] do
    let input := s!"(set-logic {logic})(declare-const x Real)(assert (= (+ x 1) 2))(check-sat)"
    (parseAndInspectQuery input fun query => do
      require (query.logic == some logic) "lost Real logic"
      require (query.assertionTerms.size == 1) "lost Real assertion"
    ).runIO
  for (body, ordinal, reason) in #[
    ("(assert (= (sin 1.0) 0.0))", 2, "SINE"),
    ("(define-fun bad () Real (^ 2.0 3))", 2, "POW"),
    ("(assert (= (/ true 1.0) 0.0))", 2, "arithmetic"),
    ("(assert (= (/ 1.0) 0.0))", 2, "invalid kind")
  ] do
    checkRejected "unsupported-real" s!"(set-logic ALL){body}(check-sat)" ordinal reason

def checkConversions : IO Unit := do
  let path := "tests/translation/real/conversions.smt2"
  (parseAndInspectQuery (← IO.FS.readFile path) (name := path) fun query => do
    require (query.assertionTerms.size == 12 && query.definitions.size == 2)
      "conversion fixture lost terms"
    require (!(query.invoked.any (·.startsWith "check-sat"))) "mixed query invoked a solver"
  ).runIO
  for logic in #["QF_LIRA", "QF_NIRA", "QF_UFLIRA", "QF_UFNIRA", "LIRA", "NIRA", "UFLIRA", "UFNIRA"] do
    let input := s!"(set-logic {logic})(declare-const i Int)(declare-const x Real)\
      (assert (= (to_real i) x))(assert (= (to_int x) i))(assert (is_int x))(check-sat)"
    (parseAndInspectQuery input fun query => do
      require (query.logic == some logic && query.assertionTerms.size == 3) "lost mixed logic or terms"
    ).runIO
  for body in #["(assert (= (to_real true) 0.0))", "(assert (= (to_real 1.5) 0.0))",
      "(assert (= (to_int false) 0))", "(assert (is_int true))", "(assert (is_int 1.0 2.0))"] do
    checkRejected "invalid-conversion" s!"(set-logic ALL){body}(check-sat)" 2 ""

def checkBitvectors : IO Unit := do
  let path := "tests/translation/bitvec/arithmetic.smt2"
  (parseAndInspectQuery (← IO.FS.readFile path) (name := path) fun query => do
    require (query.assertionTerms.size == 16 && query.definitions.size == 2) "BV fixture lost terms"
    let some declaration := query.declarations[0]? | throw (.error "missing BV declaration")
    require (declaration.term.getSort!.getBitVectorSize! == 4) "BV alias lost its width"
    require (!(query.invoked.any (·.startsWith "check-sat"))) "BV query invoked a solver"
  ).runIO
  for logic in #["QF_BV", "QF_UFBV", "BV", "UFBV"] do
    (parseAndInspectQuery s!"(set-logic {logic})(declare-const x (_ BitVec 8))\
      (assert (= (bvadd x #x01) #x00))(check-sat)" fun query => do
      require (query.logic == some logic && query.assertionTerms.size == 1) "lost BV logic or assertion"
    ).runIO
  for (body, ordinal, reason) in #[
    ("(declare-const x (_ BitVec 0))", 2, "Illegal bitvector size"),
    ("(define-sort Zero () (_ BitVec 0))", 2, "Illegal bitvector size"),
    ("(assert (= (_ bv256 8) #x00))", 2, "overflow"),
    ("(assert (= (bvadd #b0 #b00) #b0))", 2, "comparable bit-vector"),
    ("(declare-fun f ((_ BitVec 4)) Bool)(assert (f #x00))", 3, "type"),
    ("(assert (bvcomp #x0 #x0))", 2, "Bool"),
    ("(assert (= (bvsub #x5 #x3 #x1) #x1))", 2, "invalid kind"),
    ("(assert (bvsdivo #x8 #xf))", 2, "BITVECTOR_SDIVO")
  ] do
    checkRejected "invalid-bv" s!"(set-logic ALL){body}(check-sat)" ordinal reason
  checkRejected "qf-bv-quantifier"
    "(set-logic QF_BV)(assert (forall ((x (_ BitVec 4))) (= x x)))(check-sat)" 2 "quantif"

def checkBitvectorWidths : IO Unit := do
  let path := "tests/translation/bitvec/widths.smt2"
  (parseAndInspectQuery (← IO.FS.readFile path) (name := path) fun query => do
    require (query.assertionTerms.size == 10 && query.definitions.size == 1) "lost width-changing terms"
    require (!(query.invoked.any (·.startsWith "check-sat"))) "BV query invoked a solver"
    let concat := query.assertionTerms[0]![0]!
    require (concat.getKind! == .BITVECTOR_CONCAT && concat.getNumChildren == 3 &&
      concat.getSort!.getBitVectorSize! == 8) "concat lost operands or result width"
  ).runIO
  for (body, reason) in #[
    ("(= ((_ extract 4 0) #xf) #b01111)", "high extract index is bigger"),
    ("(= ((_ extract 0 1) #xf) #b1)", "high extract index is smaller"),
    ("(= ((_ extract 0) #xf) #b1)", "invalid number of indices"),
    ("(= ((_ extract 1 0 0) #xf) #b1)", "invalid number of indices"),
    ("(= ((_ extract -1 0) #xf) #b1)", "Negative numerals"),
    ("(= ((_ repeat 0) #xf) #xf)", "number of repeats > 0"),
    ("(= ((_ zero_extend -1) #xf) #xf)", "Negative numerals"),
    ("(= ((_ sign_extend 1) #xf #xf) #b11111)", "invalid kind"),
    ("(= (concat #xf) #xf)", "invalid kind"),
    ("(= ((_ extract 0 0) 1) #b1)", "expecting a bit-vector"),
    ("(= ((_ zero_extend 4) #xf) #xf)", "same type"),
    ("(= ((_ repeat 2) #xf) #xf)", "same type")
  ] do
    checkRejected "invalid-bv-width" s!"(set-logic ALL)(assert {body})(check-sat)" 2 reason

def checkBitvectorShifts : IO Unit := do
  let path := "tests/translation/bitvec/shifts.smt2"
  (parseAndInspectQuery (← IO.FS.readFile path) (name := path) fun query => do
    require (query.assertionTerms.size == 8 && query.definitions.size == 2) "lost shift/rotation terms"
    let some amount := query.declarations[1]? | throw (.error "missing shift amount")
    let shift := query.assertionTerms[0]![0]!
    require (shift.getKind! == .BITVECTOR_SHL && shift.getNumChildren == 2 &&
      shift[1]! == amount.term) "shift lost its variable amount"
    require (!(query.invoked.any (·.startsWith "check-sat"))) "shift query invoked a solver"
  ).runIO
  for (body, reason) in #[
    ("(= (bvshl #x1 #b1) #x2)", "comparable bit-vector"),
    ("(= (bvashr #x8 1) #xc)", "expecting a bit-vector"),
    ("(= (bvlshr #x8 #x1 #x1) #x2)", "invalid kind"),
    ("(= ((_ rotate_left -1) #x8) #x1)", "Negative numerals"),
    ("(= ((_ rotate_right 1 2) #x8) #x4)", "invalid number of indices"),
    ("(= ((_ rotate_left 1) #x8 #x1) #x1)", "invalid kind"),
    ("(= ((_ rotate_right 1) true) #b1)", "expecting a bit-vector"),
    ("(= (rotate_left #x8 #x1) #x1)", "not declared"),
    ("(= ((_ rotate_left 4294967296) #x8) #x8)", "rotation index exceeds"),
    ("(= ((_ |rotate_right| 99999999999999999999999) #x8) #x8)", "rotation index exceeds")
  ] do
    checkRejected "invalid-bv-shift" s!"(set-logic ALL)(assert {body})(check-sat)" 2 reason
  -- The guard must respect comments, strings, and quoted symbols.
  (parseAndInspectQuery "(set-logic ALL)\
    (set-info :source \"(_ rotate_left 4294967296)\")\
    (declare-const |(_ rotate_right 4294967296)| Bool)\
    (assert |(_ rotate_right 4294967296)|)\n; (_ rotate_left 4294967296)\n\
    (assert (= ((_ |rotate_left| 0) #x1) #x1))(check-sat)" fun _ => pure ()).runIO

def checkBitvectorDivision : IO Unit := do
  let path := "tests/translation/bitvec/division.smt2"
  (parseAndInspectQuery (← IO.FS.readFile path) (name := path) fun query => do
    require (query.assertionTerms.size == 6 && query.definitions.size == 1) "lost BV division terms"
    require (!(query.invoked.any (·.startsWith "check-sat"))) "BV division invoked a solver"
  ).runIO
  for op in #["bvudiv", "bvurem", "bvsdiv", "bvsrem", "bvsmod"] do
    for (args, reason) in #[
      ("#x1 #b1", "comparable bit-vector"),
      ("1 #x1", "expecting a bit-vector"),
      ("#x1", "invalid kind"),
      ("#x1 #x1 #x1", "invalid kind")
    ] do
      checkRejected "invalid-bv-division"
        s!"(set-logic ALL)(assert (= ({op} {args}) #x1))(check-sat)" 2 reason

def checkBitvectorConversions : IO Unit := do
  let path := "tests/translation/bitvec/conversions.smt2"
  (parseAndInspectQuery (← IO.FS.readFile path) (name := path) fun query => do
    require (query.assertionTerms.size == 7 && query.definitions.size == 2) "lost BV conversion terms"
    for i in [:2] do
      let equality := query.assertionTerms[i]!
      let expected := if i == 0 then cvc5.Kind.INT_TO_BITVECTOR else .BITVECTOR_UBV_TO_INT
      require (equality[0]!.getKind! == expected && equality[1]!.getKind! == expected)
        "legacy conversion alias changed its native kind"
    require (query.assertionTerms[2]![0]!.getKind! == .BITVECTOR_SBV_TO_INT) "lost signed conversion"
    require (!(query.invoked.any (·.startsWith "check-sat"))) "conversion invoked a solver"
  ).runIO
  for (body, reason) in #[
    ("(= ((_ int_to_bv 0) 1) #b1)", "expecting bit-width > 0"),
    ("(= ((_ int_to_bv -1) 1) #x1)", "Negative numerals"),
    ("(= ((_ int_to_bv 4 4) 1) #x1)", "invalid number of indices"),
    ("(= ((_ int_to_bv 4) 1.0) #x1)", "expecting integer term"),
    ("(= ((_ int_to_bv 4) true) #x1)", "expecting integer term"),
    ("(= ((_ int_to_bv 4) 1 2) #x1)", "invalid kind"),
    ("(= (ubv_to_int 1) 1)", "expecting bit-vector term"),
    ("(= (ubv_to_int #x1 #x2) 1)", "invalid kind"),
    ("(= (sbv_to_int true) 1)", "expecting bit-vector term"),
    ("(bvnego #x1 #x2)", "invalid kind"),
    ("(bvnego 1)", "expecting a bit-vector term"),
    ("(= (bv2int #xff) 255)", "not declared")
  ] do
    checkRejected "invalid-bv-conversion" s!"(set-logic ALL)(assert {body})(check-sat)" 2 reason
  for op in #["bvuaddo", "bvsaddo", "bvumulo", "bvsmulo"] do
    for (args, reason) in #[
      ("#x1 #b1", "comparable bit-vector"), ("#x1 1", "comparable bit-vector"),
      ("#x1", "invalid kind"), ("#x1 #x1 #x1", "invalid kind")
    ] do
      checkRejected "invalid-bv-overflow" s!"(set-logic QF_BV)(assert ({op} {args}))(check-sat)" 2 reason
  for op in #["int_to_bv", "int2bv", "|int_to_bv|", "|int2bv|"] do
    checkRejected "wide-bv-conversion"
      s!"(set-logic ALL)(assert (= ((_ {op} 4294967296) 1) #x1))(check-sat)" 2 "conversion width exceeds"
  -- The index guard must ignore text inside comments, strings, and quoted names.
  (parseAndInspectQuery "(set-logic ALL)\
    (set-info :source \"(_ int_to_bv 4294967296)\")\
    (declare-const |(_ int2bv 4294967296)| Bool)\
    (assert |(_ int2bv 4294967296)|)\n; (_ int_to_bv 4294967296)\n\
    (assert (= ((_ |int2bv| 8) (- 1)) #xff))(check-sat)" fun _ => pure ()).runIO

def checkArrays : IO Unit := do
  let path := "tests/translation/arrays/operations.smt2"
  checkAccepted path (← IO.FS.readFile path) #["a", "b", "i", "j", "p", "f"] 5
    (#["set-logic", "define-sort"] ++ Array.replicate 6 "declare-fun" ++
      #["define-fun"] ++ Array.replicate 5 "assert") fun query => do
      let #[a, _, i, _, _, _] := query.declarations
        | throw (.error "expected six array fixture declarations")
      let sort := a.term.getSort!
      require (sort.isArray && sort.getArrayIndexSort!.isInteger && sort.getArrayElementSort!.isInteger)
        "array alias lost its native index/element sorts"
      let read := query.assertionTerms[0]![0]!
      let write := read[0]!
      require (read.getKind! == .SELECT && write.getKind! == .STORE &&
        write[0]! == a.term && write[1]! == i.term)
        "definition expansion lost array or index identity"
  for logic in #["QF_AX", "QF_ABV", "QF_AUFBV", "QF_ALIA", "QF_AUFLIA", "QF_AUFNIA",
      "ALIA", "AUFLIA", "AUFLIRA", "AUFNIA", "AUFNIRA", "ABV", "AUFBV"] do
    checkAccepted logic s!"(set-logic {logic})(assert true)(check-sat)" #[] 1 #["set-logic", "assert"]
  for (name, input, count) in #[
    ("nested", "tests/translation/arrays/nested.smt2", 5),
    ("constants", "tests/translation/arrays/constants.smt2", 13)
  ] do
    (parseAndInspectQuery (← IO.FS.readFile input) (name := name) fun query => do
      require (query.assertionTerms.size == count) s!"{name}: wrong assertion count"
      require (!query.invoked.contains "check-sat") "array parsing invoked a solver query"
    ).runIO
  -- Retain the constructor sort even if native let expansion discards its application.
  (parseAndInspectQuery "(set-logic ALL)(assert (let ((unused ((as const (Array Int Int)) 7))) true))(check-sat)"
    fun query => do
      require (query.assertionTerms[0]!.getKind! == .CONST_BOOLEAN) "expected native let expansion"
      let values := (query.assertions.flatMap (·.arrayConstants))
      require (values.size == 1 && query.arrayConstructors.size == 1 &&
        values[0]! == query.arrayConstructors[0]!.base) "erased const-array requirement was lost"
  ).runIO
  for hint in #[":pattern ((select ((as const (Array Int Int)) 0) i))",
      ":no-pattern (select ((as const (Array Int Int)) 0) i)"] do
    (parseAndInspectQuery s!"(set-logic ALL)(assert (forall ((i Int)) (! (= i i) {hint})))(check-sat)"
      fun query => require (query.assertions.flatMap (·.arrayConstants)).isEmpty
        "nonsemantic hint introduced constant-array laws").runIO
  (parseAndInspectQuery "(set-logic ALL)(assert (forall ((i Int)) \
    (! (let ((unused ((as const (Array Int Int)) 0))) (= i i)) \
       :pattern ((select ((as const (Array Int Int)) 1) i)))))(check-sat)" fun query => do
      let values := (query.assertions.flatMap (·.arrayConstants))
      require (values.size == 1 && values[0]! == query.arrayConstructors[0]!.base)
        "hint changed the retained constant-array payload"
  ).runIO
  (parseAndInspectQuery "(set-logic ALL)(assert (= (select \
    (! ((as const (Array Int Int)) 0) :named zero) 0) 0))(check-sat)" fun query =>
      require ((query.assertions.flatMap (·.arrayConstants)).size == 1) "named array lost its constructor"
  ).runIO
  for (name, body) in #[
    ("bad-select", "(assert (= (select 0 1) 0))"),
    ("quoted-as", "(assert (= (select ((|as| const (Array Int Int)) 0) 0) 0))"),
    ("bad-index", "(declare-const a (Array Int Int))(assert (= (select a true) 0))"),
    ("bad-store", "(declare-const a (Array Int Int))(assert (= (store a 0 true) a))"),
    ("bad-arity", "(declare-const a (Array Int Int))(assert (= (store a 0) a))"),
    ("bad-constant", "(assert (= ((as const (Array Int Int)) true) ((as const (Array Int Int)) 0)))"),
    ("erased-wrong-payload", "(assert (let ((unused ((as const (Array Int Int)) true))) true))"),
    ("erased-string-array", "(assert (let ((unused ((as const (Array Int String)) \"x\"))) true))")
  ] do
    let called ← IO.mkRef false
    let result ← (parseAndInspectQuery ("(set-logic ALL)" ++ body ++ "(check-sat)")
      (fun _ => called.set true) (name := name)).run
    require (!(← called.get)) s!"{name}: invalid array reached inspect"
    match result with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError s!"{name}: invalid array was accepted")
  for input in #[
    "(set-logic ALL)(declare-const x Int)(assert (= (select ((as const (Array Int Int)) x) 0) x))(check-sat)",
    "(set-logic QF_ALIA)(assert (let ((v 7)) (= (select ((as const (Array Int Int)) v) 0) v)))(check-sat)",
    "(set-logic ALL)(assert (= (select ((as const (Array Int Int)) (! 0 :named v)) 0) v))(check-sat)",
    "(set-option :global-declarations true)(set-logic ALL)(push 1)\
      (assert (! (let ((erased ((as const (Array Int Int)) 0))) true) :named p))\
      (pop 1)(check-sat-assuming (p))"
  ] do
    (parseAndInspectSession input fun query => do
      require (!query.invoked.contains "check-sat") "constant-array adapter invoked a solver query"
      require (query.declarations.all (fun d => !d.name.startsWith "smt2lean.internal."))
        "private parser carriers became source declarations"
      require (!(arrayModelTerms query).isEmpty) "constant-array requirement was lost"
    ).runIO
  IO.println "Array parser passed: native identities, nested sorts, const payloads, aliases, and rejection cases"

end Smt2Lean.Tests.Parser
