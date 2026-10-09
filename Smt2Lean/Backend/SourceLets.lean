import Smt2Lean.Backend.Collisions

namespace Smt2Lean.Backend.SourceLets

open Collisions

def nameStem (tokens : Array String) : String := Id.run do
  let mut n := 0
  while tokens.any (fun t => (sourceName t).startsWith s!"smt2lean.let.{n}.") do
    n := n + 1
  return s!"smt2lean.let.{n}."

def markers (lets : Array SourceLet) : Array cvc5.Term :=
  lets.flatMap fun l => #[l.marker] ++ l.bindings.map (·.2)

def sourceDeclarations (lets : Array SourceLet) (terms : Array cvc5.Term) : Array cvc5.Term :=
  terms.filter fun term => !(markers lets).contains term

private def declareMarker (solver : cvc5.Solver) (symbols : cvc5.SymbolManager)
    (name : String) : cvc5.Env cvc5.Term := do
  let parser ← cvc5.InputParser.new solver (some symbols)
  parser.setStringInput s!"(declare-const {name} Bool)"
  let response ← (← parser.nextCommand).invoke solver symbols
  unless response.isEmpty || response.trimAscii.toString == "success" do
    throw (.error response)
  return (← symbols.getDeclaredTerms).back!

private def atom := SExpr.atom
private def list := SExpr.list

/- An ite with identical branches is an identity, at every supported sort.
The private condition records binding identities and RHSs (even unused ones).
Temporary source lets keep this adapter linear in the input size. -/
private partial def preserve (solver : cvc5.Solver) (symbols : cvc5.SymbolManager)
    (stem : String) (expression : SExpr) : StateT (Array SourceLet) cvc5.Env SExpr := do
  let .list items := expression | return expression
  if items[0]?.map render != some "let" then
    return .list (← items.mapM (preserve solver symbols stem))
  unless items.size == 3 do throw (.error "expected let bindings and body")
  let .list entries := items[1]! | throw (.error "expected let bindings")
  if entries.isEmpty then throw (.error "expected at least one let binding")
  let serial := (← get).size
  let rootName := s!"{stem}{serial}.root"
  let root ← declareMarker solver symbols rootName
  let mut bindings := #[]
  let mut names := #[]
  let mut values := #[]
  for entry in entries, i in [:entries.size] do
    let .list pair := entry | throw (.error "expected a let binding")
    unless pair.size == 2 do throw (.error "expected a let name and value")
    let .atom spelling := pair[0]! | throw (.error "expected a let name")
    let marker ← declareMarker solver symbols s!"{stem}{serial}.var{i}"
    bindings := bindings.push (sourceName spelling, marker)
    names := names.push pair[0]!
    values := values.push pair[1]!
  modify (·.push { marker := root, bindings })
  let mut temporaries := #[]
  let mut aliases := #[]
  let mut condition := #[atom "and", atom rootName]
  for value in values, i in [:values.size] do
    let temp := atom s!"{stem}{serial}.rhs{i}"
    temporaries := temporaries.push (list #[temp, ← preserve solver symbols stem value])
    let wrapped := list #[atom "ite", atom bindings[i]!.2.toString, temp, temp]
    aliases := aliases.push (list #[names[i]!, wrapped])
    condition := condition.push (list #[atom "=", wrapped, wrapped])
  let body ← preserve solver symbols stem items[2]!
  let result := atom s!"{stem}{serial}.body"
  return list #[atom "let", list temporaries,
    list #[atom "let", list aliases,
      list #[atom "let", list #[list #[result, body]],
        list #[atom "ite", list condition, result, result]]]]

/-- Only term-bearing source commands are adapted; native parsing still checks sorts/scopes. -/
def prepare (command : Source.Command) (solver : cvc5.Solver)
    (symbols : cvc5.SymbolManager) (stem : String) : cvc5.Env (Source.Command × Array SourceLet) := do
  unless command.tokens.contains "let" && #["assert", "define-fun", "define-fun-rec", "define-funs-rec", "define-const",
      "check-sat-assuming", "get-value"].contains (command.tokens[1]?.getD "") do
    return (command, #[])
  let (expression, stop) ← ofExcept ((Collisions.read command.tokens 0).mapError cvc5.Error.error)
  unless stop == command.tokens.size do throw (.error "unexpected trailing tokens")
  let (expression, lets) ← (preserve solver symbols s!"{stem}{command.source.number}." expression).run #[]
  let text := render expression
  return ({ command with text, tokens := Source.tokenize text }, lets)

def root? (lets : Array SourceLet) (term : cvc5.Term) : Option SourceLet := do
  guard (term.getKind! == .ITE && term[1]! == term[2]!)
  let condition := term[0]!
  guard (condition.getKind! == .AND)
  lets.find? (·.marker == condition[0]!)

def values (term : cvc5.Term) : Array cvc5.Term :=
  (term[0]!.getChildren.extract 1 term[0]!.getNumChildren).map (·[0]!)

/-- Remove only our private wrappers, never user-written conditionals. -/
partial def erase (tm : cvc5.TermManager) (lets : Array SourceLet) (root : cvc5.Term) : cvc5.Env cvc5.Term := do
  if lets.isEmpty then return root
  return (← (visit root).run {}).1
where
  visit (term : cvc5.Term) : StateT (Std.HashMap cvc5.Term cvc5.Term) cvc5.Env cvc5.Term := do
    if let some result := (← get)[term]? then return result
    let result ← if (root? lets term).isSome ||
        (term.getKind! == .ITE && (markers lets).contains term[0]! && term[1]! == term[2]!) then
      visit term[1]!
    else
      let children ← term.getChildren.mapM visit
      if children == term.getChildren then pure term else tm.mkTermOfOp (← ofExcept term.getOp) children
    modify (·.insert term result)
    return result

end Smt2Lean.Backend.SourceLets
