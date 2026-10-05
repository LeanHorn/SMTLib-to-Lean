import tests.backend.Support
import Smt2Lean.Sharing

open Lean Meta Qq Classical

namespace Smt2Lean.Tests

/-- A compact DAG whose fully expanded syntax repeats its argument many times. -/
private def repeated (x : Q(Int)) : Q(Int) := Id.run do
  let mut value : Q(Int) := q($x + 1)
  for _ in [:8] do value := q($value + $value)
  return value

private def checkShared (original : Expr) : MetaM Expr := do
  let shared ← Smt2Lean.Sharing.introduce original
  unless (shared.find? fun expression => expression.isLet).isSome do
    throwError "repeated expressions were not given local bindings"
  if shared.hasFVar || shared.hasLooseBVars || shared.hasMVar then
    throwError "sharing left unresolved variables"
  checkEqual (← inferType shared) (← inferType original)
  checkEqual shared original
  checkWithKernel shared
  return shared

private def checkScopes : MetaM Unit := do
  withLocalDeclD `shared q(Int) fun x => do
    let x : Q(Int) := x
    let term := repeated x
    let cases : Array Expr := #[
      -- A same-named inner binder must not capture the repeated outer term.
      q($term > $x ∧ ∃ shared : Int, $term + shared = $x),
      -- CHC models bind relations existentially outside universally bound terms.
      q(∃ P : Int → Prop, ∀ y : Int, P ($term + y) → P ($term - y)),
      -- Retain existing lets, including a binder whose name shadows their name.
      q(let shared := $term; let next := shared + shared;
        ∀ shared : Int, next + shared > $x),
      q(∀ p : Prop,
        (if p then $term else -$term) = $x ∧
        (if p then $term > 0 else $term < 0))]
    for expression in cases do
      discard <| checkShared (← mkForallFVars #[x] expression)

def checkSharing (env : Environment) : IO Unit := do
  discard <| checkScopes.toIO
    { fileName := "sharing", fileMap := default,
      options := Lean.maxRecDepth.set {} 4096, maxRecDepth := 4096 } { env }
  runQuery env "nested lets"
    "(set-logic QF_LIA) (declare-const x Int)\n\
     (assert (let ((a (+ x 1))) (let ((b (+ a a)))\
       (let ((c (+ b b))) (let ((d (+ c c))) (let ((e (+ d d)))\
       (let ((f (+ e e))) (let ((g (+ f f))) (let ((h (+ g g)))\
       (= (+ h h) x)))))))))) (check-sat)" fun query =>
      checkRefutation query q(∀ x : Int,
        (let a := x + 1; let b := a + a; let c := b + b; let d := c + c;
         let e := d + d; let f := e + e; let g := f + f; let h := g + g;
         h + h = x) → False)
  IO.println "Sharing passed: scopes, existing lets, CHC binders, ite, and emitted equivalence"

end Smt2Lean.Tests
