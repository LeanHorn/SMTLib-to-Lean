import Lean.Meta.Tactic.Simp.Main
import Lean.Meta.Tactic.Delta

namespace Smt2Lean.Equivalence

open Lean Meta

/-- Naming a function can change its hidden Decidable arguments. Normalize only
those arguments, with proofs; do not simplify the user's formula. -/
private def normalize (value : Expr) : MetaM Simp.Result := do
  -- This traversal covers a whole generated query, including implicit arguments.
  let context ← Simp.mkContext {
    iota := false, zeta := true, beta := true, singlePass := true, maxSteps := 1000000 }
  let (result, _) ← Simp.main value context (methods := {
    -- Normalize children first: changing an inner ite can cause congruence to
    -- synthesize a new Decidable argument for the outer condition.
    post := fun value => do
      unless value.isAppOfArity ``ite 5 do return .continue
      let args := value.getAppArgs
      let decision := mkApp (mkConst ``Classical.propDecidable) args[1]!
      if args[2]! == decision then return .continue
      let result := mkAppN value.getAppFn (args.set! 2 decision)
      let equality ← mkAppM ``Subsingleton.elim #[args[2]!, decision]
      let proof ← withLocalDeclD `decision (← inferType decision) fun d => do
        let function ← mkLambdaFVars #[d] (mkAppN value.getAppFn (args.set! 2 d))
        mkCongrArg function equality
      return .done { expr := result, proof? := some proof }
  })
  return result

/-- Produce an equality proof, allowing only unfolding and Decidable irrelevance.
The caller must submit this proof to the kernel. -/
def prove (left right : Expr) (unfold : Name → Bool) : MetaM Expr := do
  if ← isDefEq left right then return ← mkEqRefl left
  let left ← deltaExpand left unfold
  let right ← deltaExpand right unfold
  let a ← normalize left
  let b ← normalize right
  unless ← isDefEq a.expr b.expr do
    throwError "source-preserving translation changed the proposition:\n{a.expr}\nversus\n{b.expr}"
  let ha ← match a.proof? with
    | some proof => pure proof
    | none => mkEqRefl left
  let hb ← match b.proof? with
    | some proof => pure proof
    | none => mkEqRefl right
  mkEqTrans ha (← mkEqSymm hb)

end Smt2Lean.Equivalence
