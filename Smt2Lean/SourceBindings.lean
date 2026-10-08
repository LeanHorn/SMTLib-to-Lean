import Smt2Lean.Backend.SourceLets
import Smt.Reconstruct

namespace Smt2Lean.SourceBindings

open Lean Meta Backend

private def key (term : cvc5.Term) := "smt2lean.source-let:" ++ term.toString

/-- Metadata is local to the reconstruction; native objects never enter the Lean environment. -/
def context (context : Smt.Reconstruct.Context) (lets : Array SourceLet) : Smt.Reconstruct.Context :=
  { context with userNames := lets.foldl (fun names l =>
      l.bindings.foldl (fun names (name, marker) => names.insert (key marker) (mkConst (Name.mkSimple name)))
        (names.insert (key l.marker) (mkNatLit l.bindings.size))) context.userNames }

/-- Bind all RHSs in the outer scope, as required by SMT's simultaneous let. -/
partial def withBindings (terms : Array cvc5.Term) (action : Smt.ReconstructM Expr)
    : Smt.ReconstructM Expr := do
  let values ← terms.mapM fun term => Smt.Reconstruct.reconstructTerm term[1]!
  let saved := (← get).termCache
  try bind terms values 0 #[] action
  finally modify fun state => { state with termCache := saved }
where
  bind (terms : Array cvc5.Term) (values : Array Expr) (i : Nat) (locals : Array Expr)
      (action : Smt.ReconstructM Expr) : Smt.ReconstructM Expr := do
    if h : i < values.size then
      let term := terms[i]!
      let some name := (← read).userNames[key term[0]!]? | throwError "missing source let name"
      let value := values[i]
      withLetDecl (← mkFreshUserName name.constName!) (← inferType value) value fun x => do
        modify fun state => { state with termCache := state.termCache.insert term x }
        bind terms values (i + 1) (locals.push x) action
    else
      mkLetFVars locals (← action) (usedLetOnly := false) (generalizeNondepLet := false)

def reconstruct : Smt.TermReconstructor := fun term => do
  unless term.getKind! == .ITE && term[1]! == term[2]! do return none
  let condition := term[0]!
  if condition.getKind! == .AND && ((← read).userNames.contains (key condition[0]!)) then
    return ← withBindings (SourceLets.values term) (Smt.Reconstruct.reconstructTerm term[1]!)
  if (← read).userNames.contains (key condition) then
    return ← Smt.Reconstruct.reconstructTerm term[1]!
  return none

end Smt2Lean.SourceBindings
