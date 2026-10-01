import Smt2Lean.Backend.Parser

namespace Smt2Lean.Tests.Parser

open Smt2Lean.Backend

def require (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def checkAccepted (name input : String) (names : Array String) (count : Nat)
    (invoked : Array String)
    (inspect : ParsedQuery → cvc5.Env Unit := fun _ => pure ()) : IO Unit := do
  let calls ← IO.mkRef 0
  (parseAndInspectQuery input (name := name) fun query => do
    calls.modify (· + 1)
    require (query.declarations.map (·.name) == names) s!"{name}: wrong declarations"
    require (query.assertionTerms.size == count) s!"{name}: wrong assertion count"
    require (query.assertionSources.size == count) s!"{name}: missing assertion locations"
    require (query.invoked == invoked) s!"{name}: unexpected invocation trace: {query.invoked}"
    for left in query.declarations do
      for right in query.declarations do
        if left.name != right.name then
          require (left.term != right.term) s!"{name}: declaration identities collapsed"
    inspect query
  ).runIO
  require ((← calls.get) == 1) s!"{name}: expected exactly one inspection"

def checkRejected (name input : String) (ordinal : Nat) (reason : String) : IO Unit := do
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

end Smt2Lean.Tests.Parser
