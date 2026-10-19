import Lean.Meta.Tactic.Simp.Main
import Lean.Meta.Tactic.Delta
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum.Eq

namespace Smt2Lean.Equivalence

open Lean Meta Qq

/-- Only literal syntax may discharge the zero test; symbolic denominators stay untouched. -/
private partial def isRealLiteral (value : Expr) : Bool :=
  if value.isAppOfArity ``OfNat.ofNat 3 then value.getAppArgs[1]!.isRawNatLit
  else if value.isAppOfArity ``Neg.neg 3 then isRealLiteral value.appArg!
  else if value.isAppOfArity ``HDiv.hDiv 6 || value.isAppOfArity ``Div.div 4 then
    isRealLiteral value.appFn!.appArg! && isRealLiteral value.appArg!
  else false

/-- A named division can acquire a literal denominator only after unfolding.
Prove that its zero-case branch is unreachable, without changing other arithmetic. -/
private def normalizeRealDiv (value : Expr)
    (cache : IO.Ref (Std.HashMap ExprStructEq Expr)) : MetaM (Option Simp.Result) := do
  unless value.isAppOfArity `SMT.realDiv 3 do return none
  let denominator : Q(Real) := value.appArg!
  unless isRealLiteral denominator do return none
  let proof ← if let some proof := (← cache.get)[ExprStructEq.mk denominator]? then pure proof
    else do
      let ⟨false, proof⟩ ← Mathlib.Meta.NormNum.deriveBool q($denominator = (0 : Real))
        | return none
      cache.modify (·.insert (ExprStructEq.mk denominator) proof)
      pure proof
  let some conditional ← unfoldDefinition? value (ignoreTransparency := true)
    | throwError "could not unfold the Real division helper"
  unless conditional.isAppOfArity ``ite 5 do
    throwError "expected the Real division helper to unfold to a conditional"
  let args := conditional.getAppArgs
  let equality := mkAppN (mkConst ``if_neg [Level.one])
    #[args[1]!, args[2]!, proof, args[0]!, args[3]!, args[4]!]
  return some { expr := args[4]!, proof? := some equality }

/-- Normalize literal division and hidden Decidable arguments with proofs,
without simplifying the user's formula. -/
private def normalize (value : Expr) : MetaM Simp.Result := do
  let cache ← IO.mkRef ({} : Std.HashMap ExprStructEq Expr)
  -- This traversal covers a whole generated query, including implicit arguments.
  let context ← Simp.mkContext {
    iota := false, zeta := true, beta := true, singlePass := true, maxSteps := 1000000 }
  let (result, _) ← Simp.main value context (methods := {
    -- Normalize children first: changing an inner ite can cause congruence to
    -- synthesize a new Decidable argument for the outer condition.
    post := fun value => do
      if let some result ← normalizeRealDiv value cache then return .done result
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

/-- Produce an equality proof using unfolding, literal division and Decidable irrelevance.
The caller must submit this proof to the kernel. -/
def prove (left right : Expr) (unfold : Name → Bool) : MetaM Expr := do
  if ← isDefEq left right then return ← mkEqRefl left
  let left ← deltaExpand left unfold
  let right ← deltaExpand right unfold
  let a ← normalize left
  let b ← normalize right
  unless ← isDefEq a.expr b.expr do
    throwError "could not prove source-preserving translation equivalent:\n{a.expr}\nversus\n{b.expr}"
  let ha ← match a.proof? with
    | some proof => pure proof
    | none => mkEqRefl left
  let hb ← match b.proof? with
    | some proof => pure proof
    | none => mkEqRefl right
  mkEqTrans ha (← mkEqSymm hb)

end Smt2Lean.Equivalence
