import Smt2Lean.Backend

open Smt2Lean.Backend

private def smokeInput : String :=
  "(set-logic QF_UF)\n(assert (and true (not false)))\n(check-sat)"

private def require (condition : Bool) (message : String) : cvc5.Env Unit := do
  unless condition do throw (.error message)

private def checkSmoke : cvc5.Env Unit :=
  parseAndInspectQuery smokeInput fun assertions invoked => do
    require (invoked == #["set-logic", "assert"])
      s!"unexpected native invocation trace: {invoked}"
    require (assertions.size == 1) s!"expected one assertion, got {assertions.size}"
    let assertion := assertions[0]!
    let sort ← ofExcept assertion.getSort
    let kind ← ofExcept assertion.getKind
    require sort.isBoolean "expected a Bool-sorted assertion"
    require (kind == .AND) "expected an AND term"
    let args := assertion.getChildren
    require (args.size == 2) "expected two AND children"
    require (← ofExcept args[0]!.getBooleanValue) "expected true as the first child"
    let rightKind ← ofExcept args[1]!.getKind
    require (rightKind == .NOT) "expected NOT as the second child"
    let negated := args[1]!.getChildren
    require (negated.size == 1) "expected one NOT child"
    require (!(← ofExcept negated[0]!.getBooleanValue)) "expected false inside NOT"
    IO.println s!"invoked commands: {invoked}"
    IO.println "intercepted check-sat; no query invoked"
    IO.println s!"assertion: {assertion} : {sort}"
    IO.println s!"term kinds: {kind}, {← ofExcept args[0]!.getKind}, {rightKind}"

private def expectFailure (label input : String) : IO Unit := do
  let result ← (parseAndInspectQuery input (fun _ _ => pure ()) (name := label)).run
  match result with
  | .ok _ => throw (IO.userError s!"{label}: unexpectedly accepted invalid input")
  | .error e => IO.println s!"{label}: rejected as expected: {e}"

def main : IO UInt32 := do
  try
    checkSmoke.runIO
    expectFailure "malformed" "(set-logic QF_UF)\n(assert (and true (not false))"
    expectFailure "invalid-logic" "(set-logic NOT_A_LOGIC)\n(check-sat)"
    expectFailure "unsupported-query"
      "(set-logic QF_UF)\n(assert true)\n(check-sat-assuming (true))"
    expectFailure "missing-check" "(set-logic QF_UF)\n(assert true)"
    expectFailure "repeated-check" (smokeInput ++ "\n(check-sat)")
    expectFailure "trailing-command" (smokeInput ++ "\n(assert false)")
    expectFailure "malformed-tail" (smokeInput ++ "\n(assert")
    IO.println "backend parser smoke passed"
    return 0
  catch e =>
    IO.eprintln s!"backend parser smoke failed: {e}"
    return 1
