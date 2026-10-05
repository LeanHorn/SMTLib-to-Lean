import Lean.Meta.Transform

namespace Smt2Lean.Sharing

open Lean Meta

private abbrev ExprMap (α : Type) := Std.HashMap ExprStructEq α

private structure Occurrence where
  uses : Nat
  size : Nat
  deriving Inhabited

private structure Counts where
  occurrences : ExprMap Occurrence := {}
  order : Array Expr := #[]

/-- Binders delimit scopes. Applications are visited as a whole, not as partial spines. -/
private def children (value : Expr) : Array Expr :=
  match value with
  | .app .. => #[value.getAppFn] ++ value.getAppArgs
  | .mdata _ body | .proj _ _ body => #[body]
  | _ => #[]

/-- Count DAG edges, visiting shared children once. Cap sizes to avoid enormous integers. -/
private partial def count (value : Expr) : StateM Counts Nat := do
  if let some occurrence := (← get).occurrences[(ExprStructEq.mk value)]? then
    modify fun state => { state with
      occurrences := state.occurrences.insert value { occurrence with uses := 2 } }
    return occurrence.size
  let mut size := 1
  for child in children value do
    size := min 256 (size + (← count child))
  modify fun state => {
    occurrences := state.occurrences.insert value { uses := 1, size }
    order := state.order.push value }
  return size

private def replace (value : Expr) (bindings : ExprMap Expr) : CoreM Expr :=
  Core.transform value (pre := fun value => do
    if let some replacement := bindings[(ExprStructEq.mk value)]? then return .done replacement
    match value with
    | .forallE .. | .lam .. | .letE .. => return .done value
    | _ => return .continue)

/-- Introduce bindings in dependency order, then close their scope without expanding them. -/
private partial def bind (values : Array Expr) (index : Nat) (root : Expr)
    (bindings : ExprMap Expr := {}) (locals : Array Expr := #[]) : MetaM Expr := do
  if h : index < values.size then
    let original := values[index]
    let value ← replace original bindings
    let type ← inferType value
    let reducedType ← whnf type
    -- Preserve ordinary notation for type expressions, proofs, instances, and partial applications.
    if (reducedType.isSort && !reducedType.isProp) || reducedType.isForall ||
        (← isProof value) || (← isClass? type).isSome then
      return ← bind values (index + 1) root bindings locals
    withLetDecl (← mkFreshUserName `shared) type value fun x => do
      bind values (index + 1) root (bindings.insert original x) (locals.push x)
  else
    mkLetFVars locals (← replace root bindings) (generalizeNondepLet := false)

/--
Give repeated, substantial expressions local Lean names. Each binder is processed in
its own context, so a binding never crosses a variable's scope. Small expressions are
left unchanged. The result is definitionally equal to the input.
-/
partial def introduce (value : Expr) : MetaM Expr := do
  let value ← (prepare value).run
  let (size, counts) := (count value).run {}
  if size < 256 then return value
  let candidates := counts.order.filter fun value =>
    let occurrence := counts.occurrences[(ExprStructEq.mk value)]!
    value.isApp && occurrence.uses > 1 && occurrence.size >= 16
  if candidates.isEmpty then return value
  bind candidates 0 value
where
  prepare (value : Expr) : MonadCacheT ExprStructEq Expr MetaM Expr :=
    checkCache (ExprStructEq.mk value) fun _ => withIncRecDepth do
      match value with
      | .forallE name type body info =>
        let type ← introduce type
        withLocalDecl name info type fun x => do
          mkForallFVars #[x] (← introduce (body.instantiate1 x)) (usedOnly := false)
      | .lam name type body info =>
        let type ← introduce type
        withLocalDecl name info type fun x => do
          mkLambdaFVars #[x] (← introduce (body.instantiate1 x)) (usedOnly := false)
      | .letE name type value body nondep =>
        let type ← introduce type
        let value ← introduce value
        withLetDecl name type value (nondep := nondep) fun x => do
          mkLetFVars #[x] (← introduce (body.instantiate1 x))
            (usedLetOnly := false) (generalizeNondepLet := false)
      | .app .. =>
        let fn ← prepare value.getAppFn
        return mkAppN fn (← value.getAppArgs.mapM prepare)
      | .mdata _ body => return value.updateMData! (← prepare body)
      | .proj _ _ body => return value.updateProj! (← prepare body)
      | _ => return value

end Smt2Lean.Sharing
