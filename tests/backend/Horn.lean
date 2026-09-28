import Smt2Lean.Chc

open Smt2Lean.Backend Smt2Lean.Chc

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

private def checkParser : IO Unit := do
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
    let relations ← collectRelations query.declarations
    require (relations.size == 1) "expected one CHC relation"
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

private def checkFacts : IO Unit := do
  let path := "tests/translation/chc/clauses.smt2"
  let input ← IO.FS.readFile path
  (parseAndInspectQuery input (name := path) (mode := .chc) fun query => do
    let relations ← collectRelations query.declarations
    require (relations.map (·.name) == #["P", "R", "done", "True", "a b", "unused"])
      "wrong relations or missing unused declaration"
    require (relations.map (fun r => r.argumentSorts.map toString) ==
      #[#["Int"], #["Int", "Bool", "Int"], #[], #[], #["Bool", "Int"], #["Int", "Bool"]])
      "wrong relation signatures"
    for relation in relations, declaration in query.declarations do
      require (relation.term == declaration.term) "relation identity changed"
    let facts ← query.assertions.mapM (recognizeFact relations)
    require (facts.map (·.relation.term) == (query.declarations.extract 0 5).map (·.term))
      "facts refer to the wrong declarations"
    require (facts.map (fun f => f.arguments.map toString) ==
      #[#["0"], #["7", "(and true (not false))", "(- 9 4)"], #[], #[], #["(= 1 2)", "(+ 10 2)"]])
      "fact arguments changed or were reordered"
  ).runIO

private def expectError (name reason : String) (action : cvc5.Env Unit) : IO Unit := do
  match ← action.run with
  | .ok _ => throw (IO.userError s!"{name}: unexpectedly accepted")
  | .error error =>
    require ((toString error).contains reason) s!"{name}: wrong diagnostic: {error}"

private def checkRejectedFacts : IO Unit := do
  for (name, body, reason) in #[
    ("integer-constant", "(declare-const x Int)", "unsupported CHC declaration 'x'"),
    ("integer-function", "(declare-fun f (Int) Int)", "unsupported CHC declaration 'f'"),
    ("real-domain", "(declare-fun P (Real) Bool)", "unsupported declaration sort"),
    ("nested-relation", "(declare-fun P (Int) Bool)\n(declare-fun R (Bool) Bool)\n(assert (R (P 0)))",
      "relation inside a relation argument"),
    ("hidden-relation", "(declare-fun P (Int) Bool)\n(declare-fun R (Bool) Bool)\n(assert (R (not (P 0))))",
      "relation inside a relation argument"),
    ("nullary-argument", "(declare-const p Bool)\n(declare-fun R (Bool) Bool)\n(assert (R p))",
      "relation inside a relation argument"),
    ("literal", "(assert true)", "expected a relation fact"),
    ("negative-fact", "(declare-const p Bool)\n(assert (not p))", "expected a relation fact")
  ] do
    expectError name reason <| parseAndInspectQuery
      ("(set-logic HORN)\n" ++ body ++ "\n(check-sat)") (name := name) (mode := .chc)
      fun query => do
        let relations ← collectRelations query.declarations
        for assertion in query.assertions do discard <| recognizeFact relations assertion

private def checkBoundData : IO Unit := do
  let input := "(set-logic HORN)\n(declare-const p Bool)\n(declare-fun R (Bool) Bool)\n" ++
    "(assert (forall ((p Bool)) (R p)))\n(check-sat)"
  (parseAndInspectQuery input (mode := .chc) fun query => do
    let relations ← collectRelations query.declarations
    let quantified := query.assertions[0]!
    let bound := quantified[0]![0]!
    let some atom ← relationAtom? relations quantified[1]!
      | throw (.error "expected R applied to a bound Bool variable")
    require (atom.relation.name == "R" && atom.arguments == #[bound])
      "bound Bool argument lost its identity"
    require ((← relationAtom? relations bound).isNone)
      "bound Bool variable was mistaken for the nullary relation named p"
  ).runIO

private def checkNativeIdentity : IO Unit :=
  expectError "native identity" "undeclared CHC relation" do
    let tm ← cvc5.TermManager.new
    let bool ← tm.getBooleanSort
    let declared ← tm.mkConst bool "P"
    let other ← tm.mkConst bool "P"
    let relations ← collectRelations #[{ name := "P", term := declared }]
    require (declared != other) "expected distinct native symbols"
    discard <| recognizeFact relations other

def main : IO Unit := do
  checkParser
  checkFacts
  checkRejectedFacts
  checkBoundData
  checkNativeIdentity
  IO.println "Horn checks passed: lh_sum_rec parsed; 6 relations and 5 facts recognized"
  IO.println "No solver query invoked. Quantified facts and rules follow in 7.3."
