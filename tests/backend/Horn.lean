import Smt2Lean.Backend

open Smt2Lean.Backend

private def require (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def checkRejected (name input : String) (ordinal : Nat) (reason : String)
    (mode : ParseMode := .chc) : IO Unit := do
  let inspected ← IO.mkRef false
  let result ← (parseAndInspectQuery input (fun _ => inspected.set true)
    (name := name) (mode := mode)).run
  require (!(← inspected.get)) s!"{name}: invalid input reached inspect"
  match result with
  | .ok _ => throw (IO.userError s!"{name}: unexpectedly accepted")
  | .error error =>
    let message := toString error
    require (message.contains s!"{name}: command {ordinal}:" && message.contains reason)
      s!"{name}: wrong diagnostic: {message}"

def main : IO Unit := do
  let path := "tests/chc/lh_sum_rec.smt2"
  let input ← IO.FS.readFile path
  let calls ← IO.mkRef 0
  (parseAndInspectQuery input (name := path) (mode := .chc) fun query => do
    calls.modify (· + 1)
    let #[relation] := query.declarations
      | throw (.error "expected one declaration")
    require (relation.name == "k_1") "expected k_1"
    let signature ← ofExcept relation.term.getSort
    require (signature.isFunction) "expected a function declaration"
    let domains ← ofExcept signature.getFunctionDomainSorts
    require (domains.size == 1 && domains.all (·.isInteger) &&
      (← ofExcept signature.getFunctionCodomainSort).isBoolean)
      "expected k_1 : Int → Bool"
    require (query.assertions.size == 3) "expected three assertions"
    for assertion in query.assertions do
      require ((← ofExcept assertion.getSort).isBoolean &&
        (← ofExcept assertion.getKind) == .FORALL)
        "expected a universally quantified Bool assertion"
    require (query.invoked == #["set-logic", "declare-fun", "assert", "assert", "assert"])
      s!"unexpected invocation trace: {query.invoked}"
  ).runIO
  require ((← calls.get) == 1) "expected exactly one inspection"
  checkRejected path input 1 "unsupported logic" (mode := .smt)
  -- CHC mode uses the same sort, operator, and command checks as ordinary SMT.
  for (name, suffix, ordinal, reason) in #[
    ("bound-real", "(assert (forall ((x Real)) true))\n(check-sat)",
      2, "unsupported bound variable sort"),
    ("ite", "(assert (forall ((p Bool)) (ite p true false)))\n(check-sat)",
      2, "unsupported operator: ITE"),
    ("missing-check", "(assert true)", 3, "expected one check-sat"),
    ("repeated-check", "(check-sat)\n(check-sat)", 3, "after check-sat"),
    ("trailing-command", "(check-sat)\n(push 1)", 3, "after check-sat")
  ] do
    checkRejected s!"horn-{name}" ("(set-logic HORN)\n" ++ suffix) ordinal reason
  IO.println "Horn parser passed: lh_sum_rec, 1 declaration, 3 assertions; no solver query invoked"
  IO.println "Horn clause-shape validation is not implemented yet."
