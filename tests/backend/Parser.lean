import Smt2Lean.Backend.Parser

open Smt2Lean.Backend

private def fixtureDir : System.FilePath := "tests/translation/bool"

private def require (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def checkAccepted (name input : String) (names : Array String) (count : Nat)
    (invoked : Array String)
    (inspect : ParsedQuery → cvc5.Env Unit := fun _ => pure ()) : IO Unit := do
  let calls ← IO.mkRef 0
  (parseAndInspectQuery input (name := name) fun query => do
    calls.modify (· + 1)
    require (query.declarations.map (·.name) == names) s!"{name}: wrong declarations"
    require (query.assertions.size == count) s!"{name}: wrong assertion count"
    require (query.assertionSources.size == count) s!"{name}: missing assertion locations"
    require (query.invoked == invoked) s!"{name}: unexpected invocation trace: {query.invoked}"
    for left in query.declarations do
      for right in query.declarations do
        if left.name != right.name then
          require (left.term != right.term) s!"{name}: declaration identities collapsed"
    inspect query
  ).runIO
  require ((← calls.get) == 1) s!"{name}: expected exactly one inspection"

private def checkRejected (name input : String) (ordinal : Nat) (reason : String) : IO Unit := do
  let inspected ← IO.mkRef false
  let result ← (parseAndInspectQuery input
    (fun _ => inspected.set true) (name := name)).run
  require (!(← inspected.get)) s!"{name}: invalid input reached inspect"
  match result with
  | .ok _ => throw (IO.userError s!"{name}: unexpectedly accepted")
  | .error error =>
    let message := toString error
    require (message.contains s!"{name}:" && (message.contains s!": command {ordinal}:" || message.contains s!": command {ordinal} (:named "))
      s!"{name}: wrong error location: {message}"
    require (message.contains reason) s!"{name}: wrong rejection reason: {message}"

private def checkConnectives (name input : String) : IO Unit :=
  checkAccepted name input #["True", "a b", "p", "q", "r", "unused"] 17
    (#["set-logic"] ++ Array.replicate 6 "declare-fun" ++ Array.replicate 17 "assert")
    fun query => do
      require (query.assertions[0]? == query.declarations[0]?.map (·.term))
        s!"{name}: |True| must refer to the declared variable, not the Boolean literal"

private def checkAcceptedQueries : IO Unit := do
  let contradiction ← IO.FS.readFile (fixtureDir / "contradiction.smt2")
  let connectives ← IO.FS.readFile (fixtureDir / "connectives.smt2")
  let empty ← IO.FS.readFile (fixtureDir / "empty.smt2")
  checkAccepted "contradiction.smt2" contradiction #["p"] 2
    #["set-logic", "declare-fun", "assert", "assert"]
    fun query => require (query.logic == some "QF_UF") "expected the parsed logic"
  -- Reuse the same scripts for optional logic, empty assertions, and metadata.
  checkAccepted "contradiction.smt2 (no logic)"
    (contradiction.replace "(set-logic QF_UF)" "") #["p"] 2
    #["declare-fun", "assert", "assert"]
    fun query => require query.logic.isNone "an omitted logic must remain absent"
  checkAccepted "empty.smt2" empty #[] 0 #["set-logic"]
  checkAccepted "empty.smt2 (unused declaration)"
    (empty.replace "(check-sat)" "(declare-const unused Bool)\n(check-sat)")
    #["unused"] 0 #["set-logic", "declare-fun"]
  for status in #["sat", "unsat", "unknown"] do
    checkConnectives s!"connectives.smt2 (status {status})"
      (connectives.replace ":status sat" s!":status {status}")
  checkConnectives "connectives.smt2 (ALL)"
    (connectives.replace "(set-logic QF_UF)" "(set-logic ALL)")
  let integers ← IO.FS.readFile "tests/translation/int/literals.smt2"
  for logic in #["QF_LIA", "QF_NIA", "ALL", ""] do
    let command := if logic.isEmpty then "" else s!"(set-logic {logic})"
    let trace := if logic.isEmpty then #[] else #["set-logic"]
    checkAccepted s!"literals.smt2 ({logic})"
      (integers.replace "(set-logic QF_LIA)" command) #["Int", "flag", "a b", "unused"] 5
      (trace ++ Array.replicate 4 "declare-fun" ++ Array.replicate 5 "assert")
      fun query => do
        let #[x, flag, _, _] := query.declarations
          | throw (.error "expected four declarations")
        require ((← ofExcept x.term.getSort).isInteger)
          "expected an Int declaration"
        require ((← ofExcept flag.term.getSort).isBoolean)
          "expected a Bool declaration"
  let arithmetic ← IO.FS.readFile "tests/translation/int/arithmetic.smt2"
  checkAccepted "arithmetic.smt2" arithmetic #["x", "y", "z", "p"] 15
    (#["set-logic"] ++ Array.replicate 4 "declare-fun" ++ Array.replicate 15 "assert")
    fun query => do
      let chainGroups := query.assertions.back![1]!.getChildren
      require (chainGroups.size == 4) "expected all four comparison chains"
      for chain in chainGroups do
        require ((← ofExcept chain.getKind) == .AND && chain.getNumChildren == 3)
          "a four-operand chain must produce three comparisons"
        for comparison in chain.getChildren do
          require (comparison.getNumChildren == 2) "expected a binary comparison"
  let bounds ← IO.FS.readFile "tests/translation/int/bounds.smt2"
  checkAccepted "bounds.smt2" bounds #["x"] 2
    #["set-logic", "declare-fun", "assert", "assert"]
  let bindings ← IO.FS.readFile "tests/translation/bindings/simultaneous.smt2"
  checkAccepted "simultaneous.smt2" bindings #["x", "p"] 9
    (#["set-logic", "declare-fun", "declare-fun"] ++ Array.replicate 9 "assert")
    fun query => do
      let #[x, p] := query.declarations | throw (.error "expected two declarations")
      require (query.assertions[0]![0]! == x.term && query.assertions[1]! == query.assertions[0]!)
        "let binding order changed the outer Int reference"
      require (query.assertions[2]![0]! == p.term)
        "let binding captured the outer Bool reference"
      let swapped := query.assertions[4]!
      require (swapped[0]! == p.term && swapped[1]![0]! == x.term)
        "simultaneous bindings lost their outer identities across sorts"
  let functions ← IO.FS.readFile "tests/translation/functions/applications.smt2"
  for logic in #["QF_UFLIA", "QF_UFNIA", "ALL"] do
    checkAccepted s!"applications.smt2 ({logic})"
      (functions.replace "QF_UFLIA" logic)
      #["f", "g", "Int.add", "unused", "x", "y", "p", "P", "R", "b", "choose", "test", "True", "unusedBool"] 16
      (#["set-logic"] ++ Array.replicate 14 "declare-fun" ++ Array.replicate 16 "assert")
      fun query => do
        let #[_, g, _, _, x, y, _, _, _, _, _, _, _, _] := query.declarations
          | throw (.error "expected fourteen declarations")
        let application := query.assertions[0]![0]!
        require ((← ofExcept application.getKind) == .APPLY_UF)
          "expected an uninterpreted function application"
        require (application.getChildren == #[g.term, x.term, y.term])
          "function identity or argument order changed"
  let congruence ← IO.FS.readFile "tests/translation/functions/congruence.smt2"
  checkAccepted "congruence.smt2" congruence #["f", "x", "y"] 2
    (#["set-logic"] ++ Array.replicate 3 "declare-fun" ++ Array.replicate 2 "assert")
  let scopes ← IO.FS.readFile "tests/translation/quantifiers/scopes.smt2"
  for logic in #["UFLIA", "UFNIA", "ALL"] do
    checkAccepted s!"scopes.smt2 ({logic})" (scopes.replace "UFLIA" logic)
      #["x", "p", "R", "f", "True"] 9
      (#["set-logic"] ++ Array.replicate 5 "declare-fun" ++ Array.replicate 9 "assert")
      fun query => do
        let outer := query.assertions[3]!
        let body := outer[1]!
        let inner := body[0]!
        let outerVar := outer[0]![0]!
        let innerVar := inner[0]![0]!
        require (outerVar != innerVar && inner[1]![1]! == outerVar && inner[1]![2]! == innerVar)
          "shadowed variables lost their native identity"
  let quantified ← IO.FS.readFile "tests/translation/quantifiers/quantified.smt2"
  checkAccepted "quantified.smt2" quantified #["P"] 2
    #["set-logic", "declare-fun", "assert", "assert"]
  for logic in #["LIA", "NIA"] do
    checkAccepted s!"integer binders ({logic})"
      s!"(set-logic {logic})\n(assert (forall ((x Int)) (exists ((y Int)) (= x y))))\n(check-sat)"
      #[] 1 #["set-logic", "assert"]
  checkAccepted "Boolean binders (UF)"
    "(set-logic UF)\n(assert (forall ((p Bool)) (exists ((q Bool)) (= p q))))\n(check-sat)"
    #[] 1 #["set-logic", "assert"]

private def checkSolverOptions : IO Unit := do
  let path := "tests/translation/bool/options.smt2"
  checkAccepted path (← IO.FS.readFile path) #["p"] 2
    #["set-logic", "declare-fun", "assert", "assert"] fun query => do
    require (query.commands.size == 23 &&
      (query.commands.filter (·.text.startsWith "(set-option")).size == 10)
      "configuration commands were lost or executed"
    require (query.commands[17]!.text.contains "preserve comments" &&
      query.commands[17]!.source.number == 18 &&
      query.assertionSources.map (·.number) == #[14, 20] &&
      query.source.map (·.number) == some 21) "configuration lost its original source"
    let #[declaration] := query.declarations | throw (.error "expected one declaration")
    let p := declaration.term
    require (query.assertions[0]! == p && (← ofExcept query.assertions[1]!.getKind) == .NOT &&
      query.assertions[1]![0]! == p) "configuration changed the assertions"
  for key in #[":produce-models", ":produce-proofs", ":produce-unsat-cores", ":print-success"] do
    for value in #["1", "yes", "TRUE", "\"true\"", "|true|", "(true)", "falsehood"] do
      checkRejected s!"invalid-{key}"
        s!"(set-logic ALL)\n(set-option {key} {value})\n(check-sat)"
        2 s!"invalid value for {key}"
  for value in #["-1", "+1", "01", "1.0", "true", "\"42\"", "|42|", "#x2a", "(42)", "(- 1)"] do
    checkRejected "invalid-seed"
      s!"(set-logic ALL)\n(set-option :random-seed {value})\n(check-sat)"
      2 "invalid value for :random-seed"
  for (key, value) in #[(":incremental", "true"), (":produce-assertions", "true"), (":produce-models-extra", "true"),
      (":unknown", "false"), (":regular-output-channel", "\"ignored.log\"")] do
    checkRejected s!"unsupported-{key}"
      s!"(set-logic ALL)\n(set-option {key} {value})\n(check-sat)"
      2 "unsupported solver option"
  for (input, ordinal, reason) in #[
    ("(set-option :produce-models)", 1, "Mismatched parentheses"),
    ("(set-option :random-seed 1 2)", 1, "Expected a RPAREN_TOK"),
    ("(set-info :unknown true)\n(check-sat)", 1, "unsupported metadata"),
    ("(set-info :global-declarations true)\n(check-sat)", 1, "unsupported metadata"),
    ("(set-info :smt-lib-version 2.7)\n(check-sat)", 1, "unsupported metadata"),
    ("(set-option :produce-models true)\n(set-logic ALL)", 3, "expected one check-sat"),
    ("(set-logic ALL)\n(check-sat)\n(set-option :print-success false)", 3, "after check-sat"),
    ("(set-logic ALL)\n(check-sat)\n(exit)\n(set-option :produce-models true)", 4, "after exit")
  ] do checkRejected "invalid-configuration" input ordinal reason
  -- Enabling output production must not enable query commands.
  for command in #["(get-model)", "(get-proof)", "(get-unsat-core)", "(get-option :produce-models)",
      "(push 1)", "(reset)"] do
    let input := "(set-option :produce-models true)\n(set-option :produce-proofs true)\n" ++
      "(set-option :produce-unsat-cores true)\n(set-logic ALL)\n" ++ command ++ "\n(check-sat)"
    checkRejected s!"configured-{command}" input 5 "unsupported command"
  checkRejected "configured-model-after-check"
    "(set-option :produce-models true)\n(set-logic ALL)\n(check-sat)\n(get-model)"
    4 "after check-sat"

private def checkSessions : IO Unit := do
  let path := "tests/translation/sessions/smt.smt2"
  let seen ← IO.mkRef (#[] : Array (Array Nat))
  (parseAndInspectSession (← IO.FS.readFile path) (name := path) fun query => do
    let i := (← seen.get).size
    require (query.number == i + 1) "wrong query number"
    require (query.assertions.size == #[1, 2, 3, 2, 1, 3, 2, 2][i]!) "wrong active assertion count"
    require (query.definitions.size == #[0, 1, 1, 1, 0, 1, 1, 1][i]!) "popped definition leaked"
    require (query.declarations.map (·.name) ==
      #[#["p"], #["p", "x"], #["p", "x", "q"], #["p", "x"], #["p"], #["p", "x"], #["p", "x"], #["p", "x"]][i]!)
      "wrong active declarations"
    require (query.commands.back!.text == "(check-sat)" &&
      query.source.map (·.number) == some query.commands.back!.source.number &&
      (query.commands.filter (·.text == "(check-sat)")).size == query.number)
      "query lost its source or command history"
    require (!query.invoked.contains "check-sat") "a solver query was invoked"
    for term in query.assertions do validateAssertion term query.declarations
    let ids ← query.declarations.mapM (fun d => ofExcept d.term.getId)
    seen.modify (·.push ids)
  ).runIO
  let ids ← seen.get
  require (ids.size == 8 && ids[1]! == ids[3]! && ids[0]! == ids[4]! && ids[6]! == ids[7]!)
    "scope restoration changed declaration identities"
  require (ids[1]![1]! != ids[5]![1]! && ids[1]![1]! != ids[6]![1]!)
    "redeclared names reused native identities"
  let calls ← IO.mkRef 0
  (parseAndInspectSession "(set-logic ALL) (check-sat) (check-sat) (push 2)" fun query => do
    calls.modify (· + 1)
    require (query.assertions.isEmpty && query.declarations.isEmpty) "empty checks gained assertions"
  ).runIO
  require ((← calls.get) == 2) "repeated checks or an open final scope were lost"
  for (body, checks, command, reason) in #[
    ("", 0, 2, "expected at least one check-sat"),
    ("(pop 1)", 0, 2, "exceeds active scope depth"),
    ("(push 2)\n(pop 3)", 0, 3, "exceeds active scope depth"),
    ("(push -1)", 0, 2, "expected one SMT-LIB numeral"),
    ("(push 01)", 0, 2, "expected one SMT-LIB numeral"),
    ("(push)", 0, 2, "expected one SMT-LIB numeral"),
    ("(pop 0 0)", 0, 2, "expected one SMT-LIB numeral"),
    ("(push 4294967296)", 0, 2, "UInt32 limit"),
    ("(check-sat)\n(assert (= (^ 1 0) 0))", 1, 3, "POW"),
    ("(check-sat)\n(assert", 1, 3, "unterminated command"),
    ("(check-sat)\n(exit)\n(pop 1)", 1, 4, "after exit"),
    ("(push 1)\n(declare-const x Int)\n(check-sat)\n(pop 1)\n(assert (= x 0))", 1, 6, "not declared"),
    ("(push 1)\n(define-fun f () Int 0)\n(check-sat)\n(pop 1)\n(assert (= f 0))", 1, 6, "not declared"),
    ("(push 1)\n(define-sort I () Int)\n(check-sat)\n(pop 1)\n(declare-const x I)", 1, 6, "not declared"),
    ("(push 1)\n(assert (! true :named p))\n(check-sat)\n(pop 1)\n(assert p)", 1, 6, "not declared"),
    ("(push 1)\n(define-fun bad () Int (^ 1 0))\n(pop 1)\n(check-sat)", 0, 3, "POW")
  ] do
    let calls ← IO.mkRef 0
    let result ← (parseAndInspectSession ("(set-logic ALL)\n" ++ body)
      (fun _ => calls.modify (· + 1)) (name := "bad-session.smt2")).run
    require ((← calls.get) == checks) "callback was not called at each valid check"
    match result with
    | .ok _ => throw (IO.userError "accepted an invalid session")
    | .error error =>
      let message := toString error
      require (message.contains "bad-session.smt2:" && message.contains s!"command {command}:" &&
        message.contains reason) s!"wrong session diagnostic: {message}"
      if checks > 0 then require (message.contains s!"query {checks + 1}:") "lost query number"
  IO.println "Sessions passed: active scopes, native identities, source history, and later failures"

private def checkDefinitions : IO Unit := do
  let path := "tests/translation/bindings/definitions.smt2"
  checkAccepted path (← IO.FS.readFile path) #["x", "p", "f", "later"] 8
    (#["set-logic"] ++ Array.replicate 5 "define-sort" ++ Array.replicate 3 "declare-fun" ++
      Array.replicate 8 "define-fun" ++ #["assert", "define-fun", "define-fun"] ++
      Array.replicate 6 "assert" ++ #["declare-fun", "assert"])
    fun query => do
      require (query.definitions.size == 10) "lost checked definitions"
      for definition in query.definitions do
        require (query.commands[definition.source.number - 1]!.text.startsWith "(define-fun")
          "definition lost its source command"
      let some x := query.declarations[0]? | throw (.error "missing x")
      require (query.assertions[0]![0]![0]! == x.term)
        "nullary definition lost its definition-time global"
      for term in query.assertions do validateAssertion term query.declarations
  for (logic, body, trace) in #[
    ("QF_UF", "(define-fun p () Bool true)", #["define-fun"]),
    ("QF_LIA", "(define-fun id ((x Int)) Int x)", #["define-fun"]),
    ("ALL", "(define-sort |Alias (;)| (|T (;) |) |T (;) |)", #["define-sort"]),
    ("ALL", "(define-sort Ignore (T) Int) (define-sort Chain (T) (Ignore T))",
      #["define-sort", "define-sort"])
  ] do
    checkAccepted "unused definitions" s!"(set-logic {logic})\n{body}\n(check-sat)"
      #[] 0 (#["set-logic"] ++ trace)
  -- A linear native DAG must not be traversed as an exponentially large tree.
  let mut shared := "(set-logic QF_LIA) (define-fun f0 ((x Int)) Int (+ x 1))"
  for i in [1:33] do
    shared := shared ++ s!"(define-fun f{i} ((x Int)) Int (+ (f{i-1} x) (f{i-1} x)))"
  shared := shared ++ "(assert (= (f32 0) 0)) (check-sat)"
  checkAccepted "shared definition bodies" shared #[] 1
    (#["set-logic"] ++ Array.replicate 33 "define-fun" ++ #["assert"])

  let rejected : Array (String × String × Nat × String) := #[
    ("unused-power", "(define-fun bad () Int (^ 1 2))", 2, "POW"),
    ("unused-power-parameter", "(define-fun bad ((x Int)) Int (^ x 2))", 2, "POW"),
    ("unused-branch", "(define-fun bad () Int (ite true 0 (^ 1 0)))", 2, "POW"),
    ("unused-string", "(define-fun bad () String \"\")", 2, "unsupported definition signature"),
    ("unused-param", "(define-fun bad ((x String)) Int 0)", 2, "unsupported definition signature"),
    ("recursive", "(define-fun bad ((x Int)) Int (bad x))", 2, "not declared"),
    ("forward", "(define-fun a () Int b) (define-fun b () Int 0)", 2, "not declared"),
    ("recursive-command", "(define-fun-rec f ((x Int)) Int x)", 2, "unsupported command"),
    ("duplicate", "(define-fun f () Int 1) (define-fun f () Int 2)", 3, "f"),
    ("declare-defined", "(define-fun f () Int 1) (declare-const f Int)", 3, "f"),
    ("define-declared", "(declare-const f Int) (define-fun f () Int 1)", 3, "f"),
    ("escape", "(define-fun f ((x Int)) Int x) (assert (= x 0))", 3, "not declared"),
    ("arity", "(define-fun f ((x Int) (y Int)) Int x) (assert (= (f 1) 0))", 3, "partially apply"),
    ("argument", "(define-fun f ((x Int)) Int x) (assert (= (f true) 0))", 3, "type"),
    ("result", "(define-fun f () Int true)", 2, "invalid sort"),
    ("discarded-argument", "(define-fun f ((x Int)) Int 0) (assert (= (f (^ 1 0)) 0))", 3, "POW"),
    ("discarded-body", "(define-fun f ((x Int)) Int 0) (define-fun g () Int (f (^ 1 0)))", 3, "POW"),
    ("alias-string", "(define-sort Bad () String)", 2, "unsupported sort alias"),
    ("alias-array", "(define-sort Bad (T) (Array T T))", 2, "unsupported sort alias"),
    ("alias-bv", "(define-sort Bad () (_ BitVec 8))", 2, "unsupported sort alias"),
    ("alias-unknown", "(define-sort Bad () Missing)", 2, "declared"),
    ("alias-recursive", "(define-sort Bad () Bad)", 2, "declared"),
    ("alias-forward", "(define-sort A () B) (define-sort B () Int)", 2, "declared"),
    ("alias-arity", "(define-sort Id (T) T) (declare-const x (Id Int Bool))", 3, "arity"),
    ("alias-expansion", "(define-sort Id (T) T) (declare-const x (Id String))", 3, "unsupported declaration sort"),
    ("alias-binder", "(define-sort Id (T) T) (assert (forall ((x (Id String))) true))", 3, "unsupported bound variable sort"),
    ("after-check-definition", "(check-sat) (define-fun f () Int 0)", 3, "after check-sat"),
    ("after-check-alias", "(check-sat) (define-sort I () Int)", 3, "after check-sat")
  ]
  for (name, body, ordinal, reason) in rejected do
    checkRejected s!"definition-{name}" s!"(set-logic ALL)\n{body}\n(check-sat)" ordinal reason
  checkRejected "definition-quantified-in-qf"
    "(set-logic QF_LIA) (define-fun f () Bool (forall ((x Int)) (= x x))) (check-sat)"
    2 "quantifiers require"

private def checkNamedAssertions : IO Unit := do
  let path := "tests/translation/bindings/named.smt2"
  checkAccepted path (← IO.FS.readFile path) #["x", "p"] 7
    (#["set-logic", "declare-fun", "declare-fun", "define-fun"] ++ Array.replicate 7 "assert")
    fun query => do
      require (query.assertionSources.map (·.names) == #[#["positive"], #[], #["same body"],
        #["left (;):named", "right"], #[], #["next value"], #["line\nname", "also"]])
        "labels were lost, merged, or parsed inside quoted text"
      require (query.assertions[0]! == query.assertions[1]![0]! &&
        query.assertions[0]! == query.assertions[2]!) "named reference changed its body"
      require (query.definitions.size == 1) "native named bindings became artificial definitions"
  let invalid := "(set-logic ALL)\n  (assert (! (= (^ 1 0) 0) :named |bad body|))\n(check-sat)"
  match ← (parseAndInspectQuery invalid (fun _ => throw (.error "invalid query reached inspect"))
      (name := "named-error.smt2")).run with
  | .error (.unsupported message) =>
    require (message.contains "named-error.smt2:2:3: command 2 (:named \"bad body\"):")
      s!"parser error lost its label: {message}"
  | _ => throw (IO.userError "expected named-body rejection")
  checkAccepted "named definition body"
    "(set-logic ALL) (define-fun f () Int (! (+ 1 2) :named three)) (assert (= f three)) (check-sat)"
    #[] 1 #["set-logic", "define-fun", "assert"]
  for (name, body, ordinal, reason) in #[
    ("duplicate", "(assert (! true :named a)) (assert (! false :named a))", 3, "previously declared"),
    ("declared", "(declare-const p Bool) (assert (! true :named p))", 3, "previously declared"),
    ("defined", "(define-fun p () Bool true) (assert (! false :named p))", 3, "previously declared"),
    ("declare-named", "(assert (! true :named a)) (declare-const a Bool)", 3, "already been defined"),
    ("self", "(assert (! a :named a))", 2, "not declared"),
    ("forward", "(assert (and a (! true :named a)))", 2, "not declared"),
    ("open", "(assert (forall ((x Int)) (! (> x 0) :named bad)))", 2, "Cannot name a term in a binder"),
    ("operator", "(assert (! (= (^ 1 0) 0) :named bad))", 2, "POW"),
    ("discarded", "(assert (let ((ignored (! (^ 1 0) :named bad))) true))", 2, "POW"),
    ("discarded-sort", "(assert (let ((ignored (! \"a\" :named bad))) true))", 2, "expected Bool, Int, Real, or a declared uninterpreted sort"),
    ("unknown-attribute", "(assert (! true :unknown (:named fake)))", 2, "unsupported annotation"),
    ("after-check", "(check-sat) (assert (! true :named later))", 3, "after check-sat")
  ] do
    checkRejected s!"named-{name}" s!"(set-logic ALL)\n{body}\n(check-sat)" ordinal reason

private def checkRejectedQueries : IO Unit := do
  -- Each invalid script needs its own parse: the first error stops validation.
  let rejected : Array (String × String × Nat × String) := #[
    ("malformed", "(set-logic QF_UF)\n(assert (and true (not false))",
      2, "unexpected EOF"),
    ("invalid-logic", "(set-logic NOT_A_LOGIC)\n(check-sat)",
      1, "cannot parse logic string"),
    ("string", "(set-logic ALL)\n(declare-const x String)\n(check-sat)",
      2, "unsupported declaration sort"),
    ("array-argument", "(set-logic ALL)\n(declare-fun f ((Array Int Int)) Int)\n(check-sat)",
      2, "unsupported declaration sort"),
    ("bitvector-result", "(set-logic ALL)\n(declare-fun f (Bool) (_ BitVec 8))\n(check-sat)",
      2, "unsupported declaration sort"),
    ("string-argument", "(set-logic ALL)\n(declare-fun f (String) Int)\n(check-sat)",
      2, "unsupported declaration sort"),
    ("string-result", "(set-logic ALL)\n(declare-fun f (Int) String)\n(check-sat)",
      2, "unsupported declaration sort"),
    ("function-arity", "(set-logic QF_UFLIA)\n(declare-fun f (Int Int) Int)\n(assert (= (f 1) 0))\n(check-sat)",
      3, "partially apply"),
    ("function-argument", "(set-logic QF_UFLIA)\n(declare-fun f (Int) Int)\n(assert (= (f true) 0))\n(check-sat)",
      3, "type"),
    ("mixed-arguments", "(set-logic ALL)\n(declare-fun f (Bool Int) Bool)\n(assert (f 0 true))\n(check-sat)",
      3, "type"),
    ("higher-order-logic", "(set-logic HO_ALL)\n(check-sat)",
      1, "unsupported logic"),
    ("bound-string", "(set-logic ALL)\n(assert (forall ((x String)) true))\n(check-sat)",
      2, "unsupported bound variable sort"),
    ("quantifier-in-qf", "(set-logic QF_LIA)\n(assert (forall ((x Int)) (> x 0)))\n(check-sat)",
      2, "quantifiers require"),
    ("bound-array", "(set-logic ALL)\n(assert (exists ((a (Array Int Int))) true))\n(check-sat)",
      2, "unsupported bound variable sort"),
    ("ite-unsupported-branch", "(set-logic ALL)\n(assert (forall ((p Bool)) (= (ite p 1 (^ 1 0)) 1)))\n(check-sat)",
      2, "POW"),
    ("quantifier-weight", "(set-logic UFLIA)\n(declare-fun P (Int) Bool)\n(assert (forall ((x Int)) (! (P x) :weight 5)))\n(check-sat)",
      3, "unsupported annotation: :weight"),
    ("out-of-scope", "(set-logic ALL)\n(assert (forall ((x Int)) (= x x)))\n(assert (= x 0))\n(check-sat)",
      3, "x"),
    ("let-sibling-int", "(set-logic QF_LIA)\n(assert (let ((x 1) (y x)) (= y 1)))\n(check-sat)",
      2, "not declared"),
    ("let-sibling-bool", "(set-logic QF_UF)\n(assert (let ((p true) (q p)) q))\n(check-sat)",
      2, "not declared"),
    ("let-forward-sibling", "(set-logic QF_LIA)\n(assert (let ((y x) (x 1)) (= y 1)))\n(check-sat)",
      2, "not declared"),
    ("let-out-of-scope", "(set-logic QF_LIA)\n(assert (let ((local 1)) (= local 1)))\n(assert (= local 0))\n(check-sat)",
      3, "not declared"),
    ("let-unsupported-value", "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (let ((half (^ x 2))) (let ((copy half)) (= copy 0))))\n(check-sat)",
      3, "POW"),
    ("let-unsupported-body", "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (let ((next (+ x 1))) (= (^ next 2) 0)))\n(check-sat)",
      3, "POW"),
    ("ite-condition", "(set-logic ALL)\n(assert (ite 1 true false))\n(check-sat)",
      2, "condition"),
    ("ite-branches", "(set-logic ALL)\n(assert (ite true false 1))\n(check-sat)",
      2, "type"),
    ("ite-string", "(set-logic ALL)\n(assert (= (ite true \"a\" \"b\") \"a\"))\n(check-sat)",
      2, "expected Bool, Int, Real, or a declared uninterpreted sort"),
    ("ite-bv", "(set-logic ALL)\n(assert (= (ite true #b00 #b01) #b00))\n(check-sat)",
      2, "expected Bool, Int, Real, or a declared uninterpreted sort"),
    ("push", "(set-logic QF_UF)\n(push 1)\n(check-sat)",
      2, "unsupported command: push"),
    ("pop", "(set-logic QF_UF)\n(pop 1)\n(check-sat)",
      2, "unsupported command: pop"),
    ("horn", "(set-logic HORN)\n(assert true)\n(check-sat)",
      1, "unsupported logic"),
    ("logic", "(set-logic QF_BV)\n(assert true)\n(check-sat)",
      1, "unsupported logic"),
    ("xor-sort", "(set-logic ALL)\n(assert (xor true 1))\n(check-sat)",
      2, "Boolean subexpression"),
    ("distinct-mixed", "(set-logic ALL)\n(assert (distinct true 1))\n(check-sat)",
      2, "type"),
    ("distinct-string", "(set-logic ALL)\n(assert (distinct \"a\" \"b\"))\n(check-sat)",
      2, "expected Bool, Int, Real, or a declared uninterpreted sort"),
    ("distinct-bv", "(set-logic ALL)\n(assert (distinct #b00 #b01))\n(check-sat)",
      2, "expected Bool, Int, Real, or a declared uninterpreted sort"),
    ("string-equality", "(set-logic ALL)\n(assert (= \"a\" \"b\"))\n(check-sat)",
      2, "expected Bool, Int, Real, or a declared uninterpreted sort"),
    ("assuming", "(set-logic QF_UF)\n(check-sat-assuming (true))",
      2, "expected a user-declared"),
    ("missing-check", "(set-logic QF_UF)\n(assert true)",
      3, "expected one check-sat"),
    ("repeated-check", "(set-logic QF_UF)\n(check-sat)\n(check-sat)",
      3, "after check-sat"),
    ("after-check", "(set-logic QF_UF)\n(check-sat)\n(assert false)",
      3, "after check-sat"),
    ("command-after-check", "(set-logic QF_UF)\n(check-sat)\n(get-model)",
      3, "after check-sat"),
    ("after-exit", "(set-logic QF_UF)\n(check-sat)\n(exit)\n(assert false)",
      4, "after exit"),
    ("early-exit", "(set-logic QF_UF)\n(exit)",
      2, "exit before check-sat"),
    ("malformed-tail", "(set-logic QF_UF)\n(check-sat)\n(assert",
      3, "unexpected EOF"),
    ("undeclared", "(set-logic QF_UF)\n(assert p)\n(check-sat)",
      2, "p"),
    ("option", "(set-logic QF_UF)\n(set-option :global-declarations true)\n(check-sat)",
      2, "must be set before"),
    ("metadata", "(set-info :smt-lib-version 2.0)\n(set-logic QF_UF)\n(check-sat)",
      1, "unsupported metadata"),
    ("duplicate", "(set-logic QF_UF)\n(declare-const p Bool)\n(declare-const p Bool)\n(check-sat)",
      3, "p"),
    ("late-logic", "(declare-const p Bool)\n(set-logic QF_UF)\n(check-sat)",
      2, "set-logic")
  ]
  for (name, input, ordinal, reason) in rejected do
    checkRejected s!"reject-{name}" input ordinal reason
  for (term, kind) in #[("(xor)", "XOR"), ("(xor true)", "XOR"),
      ("(distinct)", "DISTINCT"), ("(distinct 1)", "DISTINCT"),
      ("(ite true false)", "ITE"), ("(ite true false true false)", "ITE")] do
    checkRejected s!"reject-arity-{term}"
      s!"(set-logic ALL)\n(assert {term})\n(check-sat)" 2 s!"invalid kind '{kind}'"
  -- Registering lean-smt's integer handlers must not enable unaudited operators.
  for (term, kind) in #[("(^ x 2)", "POW"), ("(^ x 0)", "POW")] do
    checkRejected s!"reject-{kind}"
      s!"(set-logic ALL)\n(declare-const x Int)\n(assert (= (+ 1 {term}) 0))\n(check-sat)"
      3 s!"unsupported operator: {kind}"

private def checkQuantifierHints : IO Unit := do
  let path := "tests/translation/quantifiers/hints.smt2"
  checkAccepted path (← IO.FS.readFile path) #["x", "P", "R"] 10
    (#["set-logic"] ++ Array.replicate 3 "declare-fun" ++ #["define-fun"] ++
      Array.replicate 10 "assert") fun query => do
    require (query.commands.any (·.text.contains ":no-pattern")) "lost original hints"
    require (query.assertionSources.flatMap (·.names) == #["allP"]) "qid became a label"
    let mut pending := query.assertions ++ query.definitions.map (·.body)
    while !pending.isEmpty do
      let term := pending.back!
      pending := pending.pop
      let kind ← ofExcept term.getKind
      require (![cvc5.Kind.INST_PATTERN_LIST, .INST_PATTERN, .INST_NO_PATTERN, .INST_ATTRIBUTE].contains kind)
        "hint reached the validated query"
      pending := pending ++ term.getChildren
  for (body, reason) in #[
    ("(! (P x) :weight true)", "unsupported annotation: :weight"),
    ("(! (P x) :unknown yes)", "unsupported annotation: :unknown"),
    ("(! (P x) :fun-def)", "unsupported annotation: :fun-def"),
    ("(! (P (^ x 2)) :pattern ((P x)))", "POW"),
    ("(! (P x) :pattern ((missing x)))", "not declared"),
    ("(! (P x) :pattern ((P true)))", "type"),
    ("(! (P x) :pattern (P x))", "fully-applied terms"),
    ("(! (P x) :qid 42)", "symbol")
  ] do
    checkRejected s!"hint-{body}"
      s!"(set-logic ALL)\n(declare-fun P (Int) Bool)\n(assert (forall ((x Int)) {body}))\n(check-sat)"
      3 reason
  for (input, ordinal, reason) in #[
    ("(set-logic QF_LIA)\n(assert (forall ((x Int)) (! (> x 0) :qid q)))\n(check-sat)",
      2, "quantifiers require"),
    ("(set-logic ALL)\n(assert (forall ((x String)) (! true :qid q)))\n(check-sat)",
      2, "unsupported bound variable sort"),
    ("(set-logic ALL)\n(assert (! true :qid q))\n(check-sat)", 2, "quantified formula bodies"),
    ("(set-logic ALL)\n(assert (forall ((x Int)) (! true :qid q)))\n(assert q)\n(check-sat)",
      3, "not declared"),
    ("(set-logic ALL)\n(define-fun unused () Bool (forall ((x Int)) (! (= (^ x 2) 0) :qid q)))\n(check-sat)",
      2, "POW"),
    ("(set-logic ALL)\n(assert (let ((unused (! (forall ((x Int)) (! (= (^ x 2) 0) :qid q)) :named bad))) true))\n(check-sat)",
      2, "POW")
  ] do checkRejected "invalid-hinted-query" input ordinal reason
  -- Check binder identity directly, not just the names printed by cvc5.
  (do
    let tm ← cvc5.TermManager.new
    let solver ← cvc5.Solver.new tm
    let parser ← cvc5.InputParser.new solver
    parser.setStringInput "(set-logic ALL) (assert (forall ((x Int)) (! (= x x) :qid q)))"
    let logic ← parser.nextCommand
    discard <| logic.invoke solver (← parser.getSymbolManager)
    let command ← parser.nextCommand
    discard <| command.invoke solver (← parser.getSymbolManager)
    let original := (← solver.getAssertions).back!
    let stripped ← withoutQuantifierHints tm original
    require (original.getNumChildren == 3 && stripped.getNumChildren == 2 &&
      stripped[0]! == original[0]! && stripped[1]! == original[1]!) "hint removal changed binders or body"
  ).runIO

/-- Reject dangling native variables even when names or already-visited terms match. -/
private def checkBoundScopes : IO Unit := (do
  let tm ← cvc5.TermManager.new
  let int ← tm.getIntegerSort
  let x ← tm.mkVar int "x"
  let other ← tm.mkVar int "x"
  let variables ← tm.mkTerm .VARIABLE_LIST #[x]
  let body ← tm.mkTerm .EQUAL #[x, x]
  let quantified ← tm.mkTerm .FORALL #[variables, body]
  validateAssertion quantified #[]
  -- Force a caller variable to share the definition's binder identity.
  let y ← tm.mkVar int "y"
  let bool ← tm.getBooleanSort
  let f ← tm.mkConst (← tm.mkFunctionSort #[int] bool) "f"
  let body ← tm.mkTerm .EXISTS #[← tm.mkTerm .VARIABLE_LIST #[y], ← tm.mkTerm .EQUAL #[x, y]]
  let source : Smt2Lean.Source.Ref := {
    file := "capture.smt2", number := 1, span := { start := {}, stop := {} } }
  let definition : ParsedDefinition := { symbol := f, parameters := #[x], body, source }
  let call ← tm.mkTerm .APPLY_UF #[f, y]
  let caller ← tm.mkTerm .FORALL #[← tm.mkTerm .VARIABLE_LIST #[y], call]
  let expanded ← expandDefinitions tm #[definition] caller
  validateAssertion expanded #[]
  let inner := expanded[1]!
  let fresh := inner[0]![0]!
  require (fresh != y && inner[1]![0]! == y && inner[1]![1]! == fresh)
    "definition substitution captured its caller's variable"
  -- The quantified occurrence is visited first; it must not validate its sibling.
  let escaped ← tm.mkTerm .AND #[body, quantified]
  let wrongIdentity ← tm.mkTerm .FORALL #[variables, ← tm.mkTerm .EQUAL #[x, other]]
  for invalid in #[escaped, wrongIdentity] do
    let error? : Option String ← try
      validateAssertion invalid #[]
      pure none
    catch error => pure (some (toString error))
    require (error?.any (fun (message : String) => message.contains "unbound variable"))
      "validation accepted a variable outside its binding scope"
  ).runIO

private def checkSourceLocations : IO Unit := do
  let input := "; ignored ( )\r\n(set-logic QF_UF)\r\n  (declare-const |p (;)| Bool)\r\n" ++
    "(assert\r\n  |p (;)|)\r\n(check-sat) ; trailing"
  checkAccepted "locations.smt2" input #["p (;)"] 1
    #["set-logic", "declare-fun", "assert"] fun query => do
      require (query.commands.size == 4) "lost source commands"
      require (query.commands[2]!.text == "(assert\r\n  |p (;)|)") "rewrote original bytes"
      let some declaration := query.declarations[0]?.bind (·.source)
        | throw (.error "missing declaration source")
      require (declaration.span.start.line == 3 && declaration.span.start.column == 3)
        "wrong declaration location"
      let source := query.assertionSources[0]!
      require (source.number == 3 && source.span.start.line == 4 && source.span.start.column == 1 &&
        source.span.stop.line == 5 && source.span.stop.column == 11) "wrong multiline assertion span"
      require (query.source.map (·.span.start.line) == some 6) "wrong check-sat location"
  for (input, location, reason) in #[
    ("; α\n(set-logic ALL)\n  (assert\n    (= (^ 1 0) 0))\n(check-sat)",
      "3:3: command 2:", "unsupported operator"),
    ("(set-logic QF_UF)\n(assert true)\n(check-sat)\n(assert",
      "4:8: command 4:", "unterminated command"),
    ("(set-logic QF_UF)\n  (assert missing)\n(check-sat)",
      "2:3: command 2:", "missing")
  ] do
    let inspected ← IO.mkRef false
    match ← (parseAndInspectQuery input (fun _ => inspected.set true) (name := "located.smt2")).run with
    | .ok _ => throw (IO.userError "accepted invalid located query")
    | .error error => require ((toString error).contains s!"located.smt2:{location}" &&
        (toString error).contains reason) s!"wrong located error: {error}"
    require (!(← inspected.get)) "invalid located query reached inspect"

private def checkAssumptions : IO Unit := do
  for input in #["(check-sat-assuming ())", "(check-sat-assuming (p))",
      "(check-sat-assuming ((not p) p p))"] do
    checkAccepted "assuming" ("(set-logic ALL)(declare-const p Bool)" ++ input)
      #["p"] (if input == "(check-sat-assuming ())" then 0 else if input == "(check-sat-assuming (p))" then 1 else 3)
      #["set-logic", "declare-fun"] fun query => do
        require (query.checkCommand == "check-sat-assuming" &&
          query.assumptionCount == query.assertions.size) "lost assumptions"
  for literal in #["true", "false", "(not true)", "(and p p)", "(not (not p))", "x", "f", "missing"] do
    let input := "(set-logic ALL)(declare-const p Bool)(declare-const x Int)" ++
      "(declare-fun f (Bool) Bool)(check-sat-assuming (" ++ literal ++ "))"
    match ← (parseAndInspectSession input (fun _ => pure ())).run with
    | .ok _ => throw (IO.userError s!"accepted invalid assumption {literal}")
    | .error _ => pure ()
  let seen ← IO.mkRef (#[] : Array Nat)
  (parseAndInspectSession "(set-logic ALL)(declare-const p Bool)(assert p)(check-sat-assuming ((not p)))(check-sat)"
    fun query => do
      require (!query.invoked.contains "check-sat-assuming") "solver invoked"
      seen.modify (·.push query.assertions.size)).runIO
  require ((← seen.get) == #[2, 1]) "assumptions leaked into next check"

private def checkResets : IO Unit := do
  let path := "tests/translation/sessions/resets.smt2"
  let seen ← IO.mkRef (#[] : Array (Nat × Nat × Nat))
  let skipped ← IO.mkRef (#[] : Array String)
  (parseAndInspectSession (← IO.FS.readFile path) (name := path)
      (onSkipped := fun command => skipped.modify (·.push command.text)) fun query => do
    require (!query.invoked.any (fun command => command.startsWith "get-" || command.startsWith "check-sat"))
      "an observational request or solver query was invoked"
    seen.modify (·.push (query.declarations.size, query.definitions.size, query.assertions.size))).runIO
  require ((← seen.get) == #[(2, 1, 3), (0, 0, 0), (1, 0, 1), (1, 1, 1),
      (1, 1, 0), (2, 1, 1), (0, 0, 0)]) "reset/global scopes changed active bindings"
  require ((← skipped.get) == #["(get-model)", "(get-value (p neg))", "(get-proof)",
      "(get-info :name)", "(get-assertions)"]) "lost unexecuted requests, including after the final check"
  for body in #[
    "(declare-const p Bool)(reset-assertions)(check-sat-assuming (p))",
    "(define-sort I () Int)(reset-assertions)(declare-const x I)",
    "(assert (! true :named label))(reset-assertions)(assert label)",
    "(check-sat)(reset)(get-model)",
    "(check-sat)(get-value ((! true :named unexpected)))",
    "(check-sat)(get-value (missing))",
    "(check-sat)(get-model extra)",
    "(reset-assertions)(set-option :global-declarations true)",
    "(reset)(set-info :smt-lib-version 2.7)"
  ] do
    match ← (parseAndInspectSession ("(set-logic ALL)" ++ body) (fun _ => pure ())).run with
    | .ok _ => throw (IO.userError s!"accepted invalid reset/request: {body}")
    | .error _ => pure ()
  -- An explicit false option, including after reset, retains local lifetimes.
  (parseAndInspectSession
    "(set-option :global-declarations false)(set-logic ALL)(reset)(set-option :global-declarations false)(set-logic ALL)(push 1)(declare-const p Bool)(pop 1)(check-sat)"
    fun query => require query.declarations.isEmpty "global option was not reset").runIO
  IO.println "Resets passed: declaration/definition lifetimes and unexecuted observational requests"

private def checkSorts : IO Unit := do
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

private def checkDivision : IO Unit := do
  let path := "tests/translation/int/division.smt2"
  (parseAndInspectQuery (← IO.FS.readFile path) (name := path) fun query => do
    require (query.assertions.size == 11 && query.definitions.size == 2) "division fixture lost terms"
    require (!(query.invoked.any (·.startsWith "check-sat"))) "division invoked a solver query"
  ).runIO
  for term in #["(div 1)", "(mod 1)", "(mod 1 2 3)", "(div true 2)", "(mod 1 false)", "(div 1.5 2)"] do
    match ← (parseAndInspectQuery s!"(set-logic ALL)(assert (= {term} 0))(check-sat)" (fun _ => pure ())).run with
    | .ok _ => throw (IO.userError s!"accepted ill-typed division: {term}")
    | .error _ => pure ()

private def checkReals : IO Unit := do
  checkAccepted "closed-real-comparison"
    "(set-logic ALL)(assert (< 1.0 2.0))(check-sat)" #[] 1 #["set-logic", "assert"]
  let path := "tests/translation/real/arithmetic.smt2"
  (parseAndInspectQuery (← IO.FS.readFile path) (name := path) fun query => do
    require (query.assertions.size == 12 && query.definitions.size == 2) "Real fixture lost terms"
    let some declaration := query.declarations[0]? | throw (.error "missing Real declaration")
    require declaration.term.getSort!.isReal "Real alias lost its sort"
    require (!(query.invoked.any (·.startsWith "check-sat"))) "Real query invoked a solver"
  ).runIO
  for logic in #["QF_LRA", "QF_NRA", "QF_UFLRA", "QF_UFNRA", "LRA", "NRA", "UFLRA", "UFNRA"] do
    let input := s!"(set-logic {logic})(declare-const x Real)(assert (= (+ x 1) 2))(check-sat)"
    (parseAndInspectQuery input fun query => do
      require (query.logic == some logic) "lost Real logic"
      require (query.assertions.size == 1) "lost Real assertion"
    ).runIO
  for (body, ordinal, reason) in #[
    ("(assert (= (sin 1.0) 0.0))", 2, "SINE"),
    ("(define-fun bad () Real (^ 2.0 3))", 2, "POW"),
    ("(assert (= (/ true 1.0) 0.0))", 2, "arithmetic"),
    ("(assert (= (/ 1.0) 0.0))", 2, "invalid kind")
  ] do
    checkRejected "unsupported-real" s!"(set-logic ALL){body}(check-sat)" ordinal reason

private def checkConversions : IO Unit := do
  let path := "tests/translation/real/conversions.smt2"
  (parseAndInspectQuery (← IO.FS.readFile path) (name := path) fun query => do
    require (query.assertions.size == 12 && query.definitions.size == 2)
      "conversion fixture lost terms"
    require (!(query.invoked.any (·.startsWith "check-sat"))) "mixed query invoked a solver"
  ).runIO
  for logic in #["QF_LIRA", "QF_NIRA", "QF_UFLIRA", "QF_UFNIRA", "LIRA", "NIRA", "UFLIRA", "UFNIRA"] do
    let input := s!"(set-logic {logic})(declare-const i Int)(declare-const x Real)\
      (assert (= (to_real i) x))(assert (= (to_int x) i))(assert (is_int x))(check-sat)"
    (parseAndInspectQuery input fun query => do
      require (query.logic == some logic && query.assertions.size == 3) "lost mixed logic or terms"
    ).runIO
  for body in #["(assert (= (to_real true) 0.0))", "(assert (= (to_real 1.5) 0.0))",
      "(assert (= (to_int false) 0))", "(assert (is_int true))", "(assert (is_int 1.0 2.0))"] do
    checkRejected "invalid-conversion" s!"(set-logic ALL){body}(check-sat)" 2 ""


def main : IO Unit := do
  checkAcceptedQueries
  checkSolverOptions
  checkSessions
  checkAssumptions
  checkResets
  checkSorts
  checkDivision
  checkReals
  checkConversions
  checkRejectedQueries
  checkDefinitions
  checkNamedAssertions
  checkQuantifierHints
  checkBoundScopes
  checkSourceLocations
  IO.println "Parser passed: Bool/Int/Real/uninterpreted-sort queries, binding identity/scope, and rejection diagnostics"
