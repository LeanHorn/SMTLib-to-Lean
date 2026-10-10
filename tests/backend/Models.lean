import Smt2Lean
import tests.backend.Support

open Lean Meta Qq Classical
open Smt2Lean Smt2Lean.Tests

private def checkValues (env : Environment) (response : Model.Response)
    (expected : Array (String × Expr)) : IO Unit := do
  let some definitions := response.definitions | throw (IO.userError "missing model")
  unless definitions.size == expected.size do throw (IO.userError "wrong model size")
  let action : MetaM Unit := do
    for (name, value) in expected do
      let some definition := definitions.find? (·.name == name)
        | throwError "missing definition {name}"
      checkEqual definition.type (← inferType value)
      checkEqual definition.value value
      for expression in #[definition.type, definition.value] do
        if expression.hasFVar || expression.hasMVar || expression.hasLooseBVars ||
            expression.getUsedConstants.any Helpers.isHelper then
          throwError "model contains unresolved variables or temporary helpers"
        -- Import already ended: check in the original environment, outside the native callback.
        checkWithKernel expression
  discard <| action.toIO { fileName := "after-import", fileMap := default } { env }

private def expectError (env : Environment) (input : String) (fragment : String := "") : IO Unit := do
  let error? ← try
    discard <| Model.importResponse input env "rejected.out"
    pure none
  catch error => pure (some error)
  let some error := error? | throw (IO.userError s!"accepted malformed/unsupported response: {input}")
  unless error.toString.contains "rejected.out" && error.toString.contains fragment do
    throw (IO.userError s!"missing diagnostic/source context: {error}")

private def checkFixtures (env : Environment) : IO Unit := do
  for solver in #["spacer", "eldarica"] do
    for stem in #["safe", "multiple", "unsafe"] do
      let name := s!"tests/models/{solver}-{stem}.out"
      let response ← Model.importResponse (← IO.FS.readFile name) env name
      unless response.status == some (if stem == "unsafe" then .unsat else .sat) do
        throw (IO.userError s!"lost solver status: {name}")
      if stem == "unsafe" then
        unless response.definitions.isNone &&
            response.diagnostics.size == (if solver == "spacer" then 1 else 0) do
          throw (IO.userError "unsat response became a model or lost the solver error")
      else
        let nonnegative := if solver == "spacer" then q(fun (x : Int) => ¬x ≤ -1)
          else q(fun (x : Int) => x ≥ 0)
        let expected := if stem == "safe" then #[ ("inv", nonnegative) ] else
          #[ ("always", q(fun (_ : Int) (_ : Prop) => True)),
             ("never", q(fun (_ : Int) => False)),
             ("nonnegative", nonnegative),
             ("positive", if solver == "spacer" then
               q(fun (x y : Int) => (¬x ≤ -1) ∧ y = 1 + x)
               else q(fun (x y : Int) => x ≥ 0 ∧ y ≥ 1)) ]
        checkValues env response expected

private def checkEnvelopes (env : Environment) : IO Unit := do
  let definitions := "(define-fun bump ((x Int)) Int (+ x 1))\n\
    (define-fun inv ((x Int) (unused Bool)) Bool (>= (bump x) 0))\n\
    (define-fun yes () Bool true)\n(define-fun no () Bool false)"
  for wrapper in #[s!"({definitions})", s!"(model {definitions})", definitions] do
    for preamble in #["", "sat\n", "; preamble\nsuccess\nsuccess\nsat\n"] do
      let response ← Model.importResponse (preamble ++ wrapper ++ "\n; trailing comment") env
      unless response.status == (if preamble.isEmpty then none else some .sat) do
        throw (IO.userError "incorrect status inference")
      checkValues env response #[ ("bump", q(fun (x : Int) => x + 1)),
        ("inv", q(fun (x : Int) (_ : Prop) => x + 1 ≥ 0)), ("yes", q(True)), ("no", q(False)) ]
  for input in #["sat ()", "sat (model)", "()", "(model)"] do
    checkValues env (← Model.importResponse input env) #[]
  for input in #["sat", "unsat", "unknown", "unknown (:reason-unknown \"timeout\")",
      "unknown (:reason-unknown incomplete)", "(error \"bad \"\"quote\"\"; (x)\")",
      "sat (error \"no model\")", "unknown (:reason-unknown \"incomplete\") (error \"no model\")"] do
    let result ← Model.importResponse input env
    unless result.definitions.isNone do throw (IO.userError "status/diagnostic became an empty model")
  let response ← Model.importResponse "unknown (:reason-unknown \"timeout\")" env
  unless response.diagnostics[0]?.map (·.message) == some "timeout" &&
      response.diagnostics[0]?.map (·.kind) == some .reasonUnknown do
    throw (IO.userError "lost unknown reason")
  let response ← Model.importResponse "(error \"bad \"\"quote\"\"; (x)\")" env
  unless response.status.isNone && response.diagnostics[0]?.map (·.message) == some "bad \"quote\"; (x)" do
    throw (IO.userError "lost error/SMT string escaping")

private def checkBindingsAndSource (env : Environment) : IO Unit := do
  let input := "; Unicode λ preamble\r\nsat\r\n(model\r\n  ; (a comment)\r\n  \
    (define-fun |inv λ;()| ((x Int)) Bool\r\n    (let ((x (+ x 1))) (and (>= x 0) (forall ((x Int)) (= x x))))))"
  let response ← Model.importResponse input env "quoted.out"
  checkValues env response #[ ("inv λ;()", q(fun (x : Int) => (x + 1 ≥ 0) ∧ ∀ y : Int, y = y)) ]
  let definition := response.definitions.get![0]!
  unless definition.source.file == "quoted.out" && definition.source.number == 1 &&
      definition.source.span.start.line == 5 && definition.source.span.start.column == 3 do
    throw (IO.userError "lost original model source location")
  let span := definition.source.span
  unless (String.fromUTF8! (input.toUTF8.extract span.start.offset span.stop.offset)).startsWith
      "(define-fun |inv λ;()|" do
    throw (IO.userError "model span is not in original UTF-8 bytes")
  let input := "sat (model (define-fun f ((x Int) (y Int)) Int\
    (let ((x y) (y x)) (- x y)))\
    (define-fun xor3 ((p Bool) (q Bool)) Bool (xor p q)))"
  let response ← Model.importResponse input env
  checkValues env response #[ ("f", q(fun (x y : Int) => y - x)),
    ("xor3", q(fun (p q : Prop) => (p ∧ ¬q) ∨ (¬p ∧ q))) ]

private def checkRejections (env : Environment) : IO Unit := do
  for input in #["", "; only comment", "success", "sat unsat", "unknown sat", "sat garbage",
      "sat () ()", "sat () (model)", "sat (model) success", "sat (model))",
      "sat (model", "sat (model (define-fun |unterminated () Bool true))",
      "sat (model (define-fun |bad\\name| () Bool true))", "(error \"unterminated)",
      "(error no-string)", "(error \"one\" \"two\")", "sat (:reason-unknown \"timeout\")",
      "unknown (:reason-unknown \"a\") (:reason-unknown \"b\")",
      "unknown (model)", "unsat (model)", "sat (error \"oops\") (model)",
      "sat (model) (error \"oops\")", "(error \"oops\") sat",
      "sat (model (assert true))", "sat (model (declare-fun f (Int) Bool))",
      "sat (model (define-fun-rec f ((x Int)) Int (f x)))",
      "sat (model (define-fun f () Int 1) (define-fun |f| () Int 2))",
      "sat (model (define-fun f ((x Int)) Int (+ x unknown)))",
      "sat (model (define-fun f () Int 1)) (define-fun g () Int 2)",
      "sat (model (define-fun f ((x Int)) Int true))",
      "sat (model (define-fun f ((x Real)) Real x))",
      "sat (model (define-fun f ((x Int)) Int (div x 0)))",
      "sat (model (define-fun f ((x Int)) Int (g x)) (define-fun g ((x Int)) Int x))",
      "unsat (forall ((x Int)) (= (inv x) (>= x 0)))"] do
    expectError env input
  -- Reject an unsupported later definition atomically, with original response coordinates.
  expectError env "sat\n(model\n(define-fun good () Bool true)\n(define-fun bad () Int missing))" "rejected.out:4:1"
  -- A failure must leave repeated imports and the original environment usable.
  checkValues env (← Model.importResponse "sat ((define-fun recovered () Bool true))" env) #[ ("recovered", q(True)) ]

def main : IO Unit := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules #[{ module := `Smt2Lean }] {} (loadExts := true)
  checkFixtures env
  checkEnvelopes env
  checkBindingsAndSource env
  checkRejections env
  IO.println "Model import passed: captured Spacer/Eldarica outputs, envelopes, statuses, diagnostics, bindings, source spans, and atomic rejections"
