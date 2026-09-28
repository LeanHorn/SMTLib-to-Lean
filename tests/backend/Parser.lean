import Smt2Lean.Backend

open Smt2Lean.Backend

private def fixtureDir : System.FilePath := "tests/translation/bool"

private def require (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def checkAccepted (name input : String) (names : Array String) (count : Nat)
    (invoked : Array String)
    (inspect : BoolQuery → cvc5.Env Unit := fun _ => pure ()) : IO Unit := do
  let calls ← IO.mkRef 0
  (parseAndInspectQuery input (name := name) fun query => do
    calls.modify (· + 1)
    require (query.declarations.map (·.name) == names) s!"{name}: wrong declarations"
    require (query.assertions.size == count) s!"{name}: wrong assertion count"
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
    require (message.contains s!"{name}: command {ordinal}:")
      s!"{name}: wrong error location: {message}"
    require (message.contains reason) s!"{name}: wrong rejection reason: {message}"

private def checkConnectives (name input : String) : IO Unit :=
  checkAccepted name input #["True", "a b", "p", "q", "r", "unused"] 9
    (#["set-logic"] ++ Array.replicate 6 "declare-fun" ++ Array.replicate 9 "assert")
    fun query => do
      require (query.assertions[0]? == query.declarations[0]?.map (·.term))
        s!"{name}: |True| must refer to the declared variable, not the Boolean literal"

private def checkAcceptedQueries : IO Unit := do
  let contradiction ← IO.FS.readFile (fixtureDir / "contradiction.smt2")
  let connectives ← IO.FS.readFile (fixtureDir / "connectives.smt2")
  let empty ← IO.FS.readFile (fixtureDir / "empty.smt2")
  checkAccepted "contradiction.smt2" contradiction #["p"] 2
    #["set-logic", "declare-fun", "assert", "assert"]
  -- Reuse the same scripts for optional logic, empty assertions, and metadata.
  checkAccepted "contradiction.smt2 (no logic)"
    (contradiction.replace "(set-logic QF_UF)" "") #["p"] 2
    #["declare-fun", "assert", "assert"]
  checkAccepted "empty.smt2" empty #[] 0 #["set-logic"]
  checkAccepted "empty.smt2 (unused declaration)"
    (empty.replace "(check-sat)" "(declare-const unused Bool)\n(check-sat)")
    #["unused"] 0 #["set-logic", "declare-fun"]
  for status in #["sat", "unsat", "unknown"] do
    checkConnectives s!"connectives.smt2 (status {status})"
      (connectives.replace ":status sat" s!":status {status}")
  checkConnectives "connectives.smt2 (ALL)"
    (connectives.replace "(set-logic QF_UF)" "(set-logic ALL)")

private def checkRejectedQueries : IO Unit := do
  -- Each invalid script needs its own parse: the first error stops validation.
  let rejected : Array (String × String × Nat × String) := #[
    ("malformed", "(set-logic QF_UF)\n(assert (and true (not false))",
      2, "EOF_TOK"),
    ("invalid-logic", "(set-logic NOT_A_LOGIC)\n(check-sat)",
      1, "cannot parse logic string"),
    ("int", "(set-logic ALL)\n(declare-const x Int)\n(check-sat)",
      2, "nullary Bool"),
    ("function", "(set-logic ALL)\n(declare-fun f (Bool) Bool)\n(check-sat)",
      2, "nullary Bool"),
    ("quantifier", "(set-logic ALL)\n(assert (forall ((p Bool)) p))\n(check-sat)",
      2, "FORALL"),
    ("ite", "(set-logic ALL)\n(declare-const p Bool)\n(assert (ite p true false))\n(check-sat)",
      3, "ITE"),
    ("push", "(set-logic QF_UF)\n(push 1)\n(check-sat)",
      2, "unsupported command: push"),
    ("pop", "(set-logic QF_UF)\n(pop 1)\n(check-sat)",
      2, "unsupported command: pop"),
    ("horn", "(set-logic HORN)\n(assert true)\n(check-sat)",
      1, "expected QF_UF or ALL"),
    ("logic", "(set-logic QF_LIA)\n(assert true)\n(check-sat)",
      1, "expected QF_UF or ALL"),
    ("xor", "(set-logic QF_UF)\n(declare-const p Bool)\n(assert (xor p true))\n(check-sat)",
      3, "XOR"),
    ("int-equality", "(set-logic ALL)\n(assert (= 1 2))\n(check-sat)",
      2, "expected Bool"),
    ("assuming", "(set-logic QF_UF)\n(check-sat-assuming ())",
      2, "unsupported command: check-sat-assuming"),
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
      3, "EOF_TOK"),
    ("undeclared", "(set-logic QF_UF)\n(assert p)\n(check-sat)",
      2, "p"),
    ("definition", "(set-logic QF_UF)\n(define-fun p () Bool true)\n(check-sat)",
      2, "unsupported command: define-fun"),
    ("option", "(set-logic QF_UF)\n(set-option :produce-models true)\n(check-sat)",
      2, "unsupported command: set-option"),
    ("metadata", "(set-info :smt-lib-version 2.0)\n(set-logic QF_UF)\n(check-sat)",
      1, "unsupported metadata"),
    ("duplicate", "(set-logic QF_UF)\n(declare-const p Bool)\n(declare-const p Bool)\n(check-sat)",
      3, "p"),
    ("late-logic", "(declare-const p Bool)\n(set-logic QF_UF)\n(check-sat)",
      2, "set-logic")
  ]
  for (name, input, ordinal, reason) in rejected do
    checkRejected s!"reject-{name}" input ordinal reason

def main : IO Unit := do
  checkAcceptedQueries
  checkRejectedQueries
  IO.println "Parser passed: 8 accepted cases, 26 rejected cases"
