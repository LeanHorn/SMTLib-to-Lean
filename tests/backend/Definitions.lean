import tests.backend.Support

open Lean Meta Qq Classical
open Smt2Lean.Backend Smt2Lean.Translate

namespace Smt2Lean.Tests

private def checkStandalone (definition : ReconstructedDefinition) (expected : Expr) : MetaM Unit := do
  for expression in #[definition.type, definition.value] do
    if expression.hasFVar || expression.hasMVar || expression.hasLooseBVars then
      throwError "standalone definition contains unresolved variables"
    if expression.getUsedConstants.any Helpers.isHelper then
      throwError "standalone definition still refers to a generated helper"
    checkWithKernel expression
  checkEqual definition.type (← inferType expected)
  checkEqual definition.value expected

private def checkStandaloneDefinitions (env : Environment) : IO Unit := do
  let input := "(set-logic ALL)\n\
    (define-fun inc ((x Int)) Int (+ x 1))\n\
    (define-fun twice ((x Int)) Int (inc (inc x)))\n\
    (define-fun inv ((x Int) (y Int)) Bool (and (>= x 0) (<= y x)))\n\
    (define-fun unused ((p Bool) (x Int)) Int 7)\n\
    (define-fun yes () Bool true)\n\
    (define-fun answer () Int (- 42))\n\
    (define-fun |inv with spaces| ((x Int)) Bool (>= (twice x) 0))\n\
    (define-fun swap ((x Int) (y Int)) Int (let ((x y) (y x)) (- x y)))\n\
    (define-fun choose ((p Bool) (x Int)) Int (ite p (inc x) x))\n\
    (define-fun half ((x Int)) Int (div x 2))\n\
    (check-sat)"
  -- Results must survive the native callback, using only the original Lean environment.
  let results ← IO.mkRef (#[] : Array ReconstructedDefinition)
  (parseAndInspectQuery input (name := "standalone.smt2") fun query => do
    let action : MetaM (Array ReconstructedDefinition) := do
      unless query.assertions.isEmpty do throwError "expected a definitions-only query"
      let first ← reconstructDefinitions query
      let second ← reconstructDefinitions query
      unless first.size == second.size do throwError "unstable definition enumeration"
      for left in first, right in second do checkEqual left.value right.value
      return first
    let (definitions, _, _) ← action.toIO { fileName := "standalone", fileMap := default } { env }
    results.set definitions
  ).runIO
  let action : MetaM Unit := do
    let definitions ← results.get
    let names := #["inc", "twice", "inv", "unused", "yes", "answer", "inv with spaces", "swap", "choose", "half"]
    unless definitions.map (·.name) == names do throwError "lost definition names or source order"
    let expected := #[q(fun (x : Int) => x + 1), q(fun (x : Int) => (x + 1) + 1),
      q(fun (x y : Int) => x ≥ 0 ∧ y ≤ x), q(fun (_ : Prop) (_ : Int) => (7 : Int)),
      q(True), q((-42 : Int)), q(fun (x : Int) => (x + 1) + 1 ≥ 0),
      q(fun (x y : Int) => y - x), q(fun (p : Prop) (x : Int) => if p then x + 1 else x),
      q(fun (x : Int) => x / 2)]
    for i in [:definitions.size] do
      let definition := definitions[i]!
      checkStandalone definition expected[i]!
      unless definition.source.file == "standalone.smt2" && definition.source.number == i + 2 do
        throwError "lost definition source location"
  discard <| action.toIO { fileName := "after-native-callback", fileMap := default } { env }

private def checkDefinitionBindings (env : Environment) : IO Unit := do
  let input := "(set-logic ALL)\n\
    (define-fun has ((x Int)) Bool (exists ((y Int)) (= x y)))\n\
    (define-fun caller ((y Int)) Bool (has y))\n\
    (define-fun shadow ((x Int)) Bool (and (> x 0) (forall ((x Int)) (= x x))))\n\
    (define-fun set.card ((false Int)) Int (+ false 1))\n\
    (define-fun |quoted caller| ((x Int)) Int (set.card x))\n\
    (define-fun exclusive ((p Bool) (q Bool)) Bool (xor p q))\n\
    (define-fun different ((x Int) (y Int) (z Int)) Bool (distinct x y z))\n\
    (assert false)\n(check-sat)"
  runQuery env "bindings.smt2" input fun query => do
    let before ← getEnv
    let handlers := (Smt.Attribute.smtExt.getState before).getD ``Smt.TermReconstructor {}
    let definitions ← reconstructDefinitions query
    let after ← getEnv
    for name in [`SMT.xor, `SMT.distinct3] do
      unless before.contains name == after.contains name do
        throwError "reconstruction leaked an operator helper"
    let current := (Smt.Attribute.smtExt.getState after).getD ``Smt.TermReconstructor {}
    unless current.size == handlers.size && current.toList.all handlers.contains do
      throwError "reconstruction changed the caller's handlers"
    let expected := #[q(fun (x : Int) => ∃ y : Int, x = y), q(fun (y : Int) => ∃ z : Int, y = z),
      q(fun (x : Int) => x > 0 ∧ ∀ y : Int, y = y), q(fun (x : Int) => x + 1),
      q(fun (x : Int) => x + 1), q(fun (p q : Prop) => (p ∧ ¬q) ∨ (¬p ∧ q)),
      q(fun (x y z : Int) => x ≠ y ∧ x ≠ z ∧ y ≠ z)]
    unless definitions.size == expected.size && definitions[3]!.name == "set.card" do
      throwError "lost definitions or renamed source symbol"
    for definition in definitions, value in expected do checkStandalone definition value

private def expectDefinitionError (query : ParsedQuery) (fragment : String) : MetaM Unit := do
  let result ← try
    discard <| reconstructDefinitions query
    pure none
  catch error => pure (some error)
  let some error := result | throwError "expected definition rejection: {fragment}"
  let message ← error.toMessageData.toString
  unless message.contains fragment && message.contains "rejected.smt2:" && message.contains "command" do
    throwError "missing definition diagnostic or source context: {message}"

private def checkDefinitionRejections (env : Environment) : IO Unit := do
  let cases := #[
    ("(declare-const external Int) (define-fun bad ((x Int)) Int (+ x external))", "undeclared term"),
    -- This SMT name exists as a Lean constant; it must not be resolved by name fallback.
    ("(declare-fun Int.add (Int Int) Int) (define-fun bad ((x Int)) Int (Int.add x x))", "undeclared term"),
    ("(define-fun bad ((x Real)) Real x)", "signatures support only Bool/Int"),
    ("(define-fun bad ((x Int)) Bool (> (to_real x) 0.0))", "bodies support only Bool/Int"),
    ("(define-fun bad ((x Int)) Int (div x 0))", "interpretation for division/modulo at zero"),
    ("(define-fun bad ((x Int) (y Int)) Int (mod x y))", "interpretation for division/modulo at zero"),
    ("(define-fun-rec bad ((x Int)) Int (ite (= x 0) 0 (bad (- x 1))))", "recursive definitions")]
  for (body, fragment) in cases do
    runQuery env "rejected.smt2" s!"(set-logic ALL) {body} (check-sat)" fun query =>
      expectDefinitionError query fragment
  runQuery env "rejected.smt2" "(set-logic ALL) (define-fun f ((x Int)) Int x) (check-sat)" fun query => do
    let some manager := query.manager | throwError "missing term manager"
    let before ← getEnv
    let body ← (do manager.mkTerm .XOR #[← manager.mkTrue, ← manager.mkFalse]).runIO
    let #[definition] := query.definitions | throwError "expected one parsed definition"
    let definition := { definition with body }
    expectDefinitionError { query with definitions := #[definition] } "declared signature"
    unless before.contains `SMT.xor == (← getEnv).contains `SMT.xor do
      throwError "failed reconstruction leaked an operator helper"
    -- A failed reconstruction must leave both the environment and handlers usable.
    let definitions ← reconstructDefinitions query
    checkStandalone definitions[0]! q(fun (x : Int) => x)

def checkDefinitionAPI (env : Environment) : IO Unit := do
  checkStandaloneDefinitions env
  checkDefinitionBindings env
  checkDefinitionRejections env
  runQuery env "empty.smt2" "(set-logic QF_LIA) (check-sat)" fun query => do
    unless (← reconstructDefinitions query).isEmpty do throwError "expected no definitions"
  IO.println "Definition API passed: closed typed values, dependencies, bindings, native lifetime, and rejection cases"

end Smt2Lean.Tests
