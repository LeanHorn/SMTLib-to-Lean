import Smt2Lean.Backend.ConstantArrays
import Smt2Lean.Backend.SourceLets

namespace Smt2Lean.Backend

/-- Counts needed to restore a local scope after native pop. -/
private structure Scope where
  sorts : Nat
  datatypes : Nat
  declarations : Nat
  definitions : Nat
  assertions : Nat
  nativeAssertions : Nat
  namedConstants : Nat
  aliases : Nat

/-- Translator state that follows native declaration and assertion scopes. -/
structure Session where
  query : ParsedQuery := {}
  arrays : ConstantArrays.State
  scopes : Array Scope := #[]
  /-- cvc5 counts defining equations as well as source assertions. -/
  nativeCount : Nat := 0
  globalDeclarations : Bool := false

def Session.mapQuery (session : Session) (f : ParsedQuery → ParsedQuery) : Session :=
  { session with query := f session.query }

def Session.depth (session : Session) : Nat := session.scopes.size

def Session.push (session : Session) (count : Nat) : Session :=
  let query := session.query
  let scope : Scope := {
    datatypes := query.datatypes.size
    sorts := query.sorts.size
    declarations := query.declarations.size, definitions := query.definitions.size
    assertions := query.assertions.size, nativeAssertions := session.nativeCount
    namedConstants := query.namedArrayConstants.size, aliases := session.arrays.aliases.size }
  { session with scopes := session.scopes ++ Array.replicate count scope }

/-- Called after native pop; global declarations survive, assertions always roll back. -/
def Session.pop (session : Session) (count : Nat) : cvc5.Env Session := do
  if count == 0 then return session
  let remaining := session.scopes.size - count
  let some scope := session.scopes[remaining]? | throw (.error "missing saved scope")
  let query := session.query
  let query := { query with
    datatypes := if session.globalDeclarations then query.datatypes else query.datatypes.extract 0 scope.datatypes
    sorts := if session.globalDeclarations then query.sorts else query.sorts.extract 0 scope.sorts
    declarations := if session.globalDeclarations then query.declarations else query.declarations.extract 0 scope.declarations
    definitions := if session.globalDeclarations then query.definitions else query.definitions.extract 0 scope.definitions
    namedArrayConstants := if session.globalDeclarations then query.namedArrayConstants else
      query.namedArrayConstants.extract 0 scope.namedConstants
    assertions := query.assertions.extract 0 scope.assertions }
  let arrays := if session.globalDeclarations then session.arrays else
    { session.arrays with aliases := session.arrays.aliases.extract 0 scope.aliases }
  return { session with
    query, arrays, scopes := session.scopes.extract 0 remaining
    nativeCount := scope.nativeAssertions +
      if session.globalDeclarations then query.definitions.size - scope.definitions else 0 }

def Session.clearAssertions (session : Session) : Session := Id.run do
  let mut query := { session.query with assertions := #[] }
  let mut arrays := session.arrays
  if !session.globalDeclarations then
    query := { query with sorts := #[], datatypes := #[], declarations := #[], definitions := #[], namedArrayConstants := #[] }
    arrays := { arrays with aliases := #[], arrayAlias := none, initialized := false }
  return { session with query, arrays, scopes := #[], nativeCount := query.definitions.size }

/-- A full reset retains source history and query numbering, but no native interpretations. -/
def Session.reset (session : Session) (arrays : ConstantArrays.State) (number : Nat) : Session :=
  { arrays, query := { number, manager := session.query.manager, commands := session.query.commands, invoked := session.query.invoked } }

/-- Check the native state after scope changes before inspecting another query. -/
def Session.checkNative (session : Session) (solver : cvc5.Solver)
    (symbols : cvc5.SymbolManager) (label : String) : cvc5.Env Unit := do
  unless (← solver.getAssertions).size == session.nativeCount &&
      SourceLets.sourceDeclarations session.query.sourceLets (ConstantArrays.sourceDeclarations session.arrays (← symbols.getDeclaredTerms)) ==
        session.query.declarations.map (·.term) &&
      (← symbols.getDeclaredSorts) == session.query.sorts.map (·.sort) do
    throw (.error s!"native and translator {label} disagree")

end Smt2Lean.Backend
