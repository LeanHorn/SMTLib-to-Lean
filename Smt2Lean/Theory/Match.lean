import Smt2Lean.Theory.Datatype
import Smt2Lean.Backend.Match

namespace Smt2Lean.Datatypes

open Lean Meta Qq

private def tester (constructor : Name) : MetaM Name := do
  let info ← getConstInfoCtor constructor
  let name := constructor.replacePrefix `SMT.Datatypes `SMT.Testers
  if (← getEnv).contains name then return name
  forallTelescope (← getConstInfoInduct info.induct).type fun parameters _ => do
    let domain := mkAppN (mkConst info.induct) parameters
    withLocalDeclD `input domain fun input => do
      let branches ← (← getConstInfoInduct info.induct).ctors.toArray.mapM fun ctor => do
        let signature ← instantiateForall (← getConstInfoCtor ctor).type parameters
        forallTelescope signature fun fields _ => do
          let value := if ctor == constructor then q(True) else q(False)
          return anonymousUnused (← mkLambdaFVars fields value (usedOnly := false))
      let value ← casesOn input q(Prop) branches
      Helpers.define name [] (← mkLambdaFVars (parameters.push input) value (usedOnly := false))

def reconstructTester : Smt.TermReconstructor := fun term => do
  unless term.getKind! == .APPLY_TESTER do return none
  let constructor ← getTesterConstructor term[0]!
  let name ← tester constructor.getAppFn.constName!
  let input ← Smt.Reconstruct.reconstructTerm term[1]!
  return mkApp (mkAppN (mkConst name) constructor.getAppArgs) input

/-- Pattern variables shadow only their own branch; cached compounds cannot cross branches. -/
private def withBindings (binders : Array cvc5.Term) (values : Array Expr)
    (body : Smt.ReconstructM Expr) : Smt.ReconstructM Expr := do
  let bindings := (← get).termCache.filter fun term value =>
    term.getKind! == .VARIABLE || term.getKind! == .CONSTANT || value.isFVar
  Smt.Reconstruct.withNewTermCache do
    let mut cache := bindings
    for binder in binders, value in values do cache := cache.insert binder value
    modify fun state => { state with termCache := cache }
    body

/-- Compile each constructor's first matching branch; catch-all variables bind the full value. -/
def reconstructMatch : Smt.TermReconstructor := fun term => do
  unless term.getKind! == .MATCH do return none
  let cases ← (Backend.readMatchCases term).runIO
  let cases ← cases.mapM fun branch => do
    let constructor ← branch.constructor.mapM fun term => do
      return (← getConstructor term).getAppFn.constName!
    return (constructor, branch)
  let input ← Smt.Reconstruct.reconstructTerm term[0]!
  let result ← Smt.Reconstruct.reconstructSort term.getSort!
  let domain ← inferType input
  let info ← getConstInfoInduct domain.getAppFn.constName!
  let branches ← info.ctors.toArray.mapM fun constructor => do
    let some (_, branch) := cases.find? (fun (name, _) => name.isNone || name == some constructor)
      | throwError "non-exhaustive datatype match"
    let signature ← instantiateForall (← getConstInfoCtor constructor).type domain.getAppArgs
    forallTelescope signature fun fields _ => do
      let values := if branch.constructor.isSome then fields else #[input]
      let value ← withBindings branch.binders values (Smt.Reconstruct.reconstructTerm branch.body)
      return anonymousUnused (← mkLambdaFVars fields value (usedOnly := false))
  return ← casesOn input result branches

end Smt2Lean.Datatypes
