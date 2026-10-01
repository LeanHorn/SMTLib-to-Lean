import Smt2Lean.Theory.Datatype
import Lean.Meta.Constructions.CasesOn

namespace Smt2Lean.Selectors

open Lean Meta Backend

private def key (selector : cvc5.Term) : String := s!"SMT.selector.{selector.getId!}"

private def anonymousUnused : Expr → Expr
  | .lam name type body info =>
    .lam (if body.hasLooseBVar 0 then name else `_) type (anonymousUnused body) info
  | value => value

/-- Include selectors inside native constant arrays, whose payloads are not children. -/
private def usedSelectors (terms : Array cvc5.Term) : Std.HashSet cvc5.Term := Id.run do
  let mut pending := terms
  let mut visited : Std.HashSet cvc5.Term := {}
  let mut selectors : Std.HashSet cvc5.Term := {}
  while !pending.isEmpty do
    let term := pending.back!
    pending := pending.pop
    if visited.contains term then continue
    visited := visited.insert term
    if term.getKind! == .APPLY_SELECTOR then selectors := selectors.insert term[0]!
    pending := pending ++ term.getChildren
    if term.isConstArray then pending := pending.push term.getConstArrayBase!
  return selectors

/-- Project the owning constructor's field; all other constructors use the whole input.
The helper and its case eliminator are checked synchronously by the kernel. -/
private def compile (typeName : Name) (constructor field : Nat) (sourceName : String)
    : MetaM Name := do
  let name := (typeName.replacePrefix `SMT.Datatypes `SMT.Selectors).str
    s!"s{constructor}_{field}_{Datatypes.namePart sourceName}"
  if (← getEnv).contains name then return name
  let info ← getConstInfoInduct typeName
  let casesName := mkCasesOnName typeName
  unless (← getEnv).contains casesName do
    let declaration ← ofExceptKernelException (mkCasesOnImp (← getEnv).toKernelEnv typeName)
    let env ← ofExceptKernelException <| (← getEnv).addDeclCore 0 1000 declaration none
    setEnv (markAuxRecursor env casesName)
  forallTelescope info.type fun parameters _ => do
    let domain := mkAppN (mkConst typeName) parameters
    let signature ← instantiateForall (← getConstInfoCtor info.ctors[constructor]!).type parameters
    let result ← forallTelescope signature fun fields _ => inferType fields[field]!
    let fallbackType ← mkArrow domain result
    let fallbackDecls := if info.ctors.length > 1 then #[(`otherwise, fallbackType)] else #[]
    withLocalDeclsDND fallbackDecls fun fallbacks =>
      withLocalDeclD `input domain fun input => do
        let alternatives ← info.ctors.toArray.mapIdxM fun i ctor => do
          let signature ← instantiateForall (← getConstInfoCtor ctor).type parameters
          forallTelescope signature fun fields _ => do
            let value := if i == constructor then fields[field]!
              else mkApp fallbacks[0]! input
            return anonymousUnused (← mkLambdaFVars fields value (usedOnly := false))
        let motive ← mkLambdaFVars #[input] result (usedOnly := false)
        let value := mkAppN (mkConst casesName [← getLevel result])
          (parameters ++ #[motive, input] ++ alternatives)
        Helpers.define name [] (← mkLambdaFVars (parameters ++ fallbacks ++ #[input]) value
          (usedOnly := false))

/-- Share one interpretation per used native selector, outside every source binder.
Single-constructor datatypes need no arbitrary choice. -/
def withInterpretations [Inhabited α] (groups : Array Datatypes.CompiledGroup)
    (terms : Array cvc5.Term) (cache : Std.HashMap cvc5.Sort Expr)
    (context : Smt.Reconstruct.Context)
    (inspect : Array Expr → Smt.Reconstruct.Context → MetaM α) : MetaM α := do
  if groups.isEmpty then return ← inspect #[] context
  let used := usedSelectors terms
  let mut selectors : Array (cvc5.Term × Expr × Bool) := #[]
  for group in groups do
    let parameters ← group.parameters.mapM fun sort => do
      let some type := cache[sort]? | throwError "missing selector field carrier: {sort}"
      return type
    for datatype in group.source.types, typeName in group.names do
      for h : i in [:datatype.constructors.size] do
        for h : j in [:datatype.constructors[i].fields.size] do
          let field := datatype.constructors[i].fields[j]
          unless used.contains field.selector do continue
          let name ← compile typeName i j field.name
          selectors := selectors.push (field.selector, mkAppN (mkConst name) parameters,
            datatype.constructors.size > 1)
  go selectors.toList #[] context
where
  go (selectors : List (cvc5.Term × Expr × Bool)) (parameters : Array Expr)
      (context : Smt.Reconstruct.Context) : MetaM α := do
    match selectors with
    | [] => inspect parameters context
    | (selector, helper, arbitrary) :: rest =>
      if arbitrary then
        let .forallE _ type _ _ ← inferType helper | throwError "selector has no fallback parameter"
        let name ← mkFreshUserName (Name.mkSimple s!"{Datatypes.namePart selector.getSymbol!}_otherwise")
        withLocalDeclD name type fun fallback => do
          let context := { context with userNames := context.userNames.insert (key selector) (mkApp helper fallback) }
          go rest (parameters.push fallback) context
      else
        go rest parameters { context with userNames := context.userNames.insert (key selector) helper }

def reconstruct : Smt.TermReconstructor := fun term => do
  unless term.getKind! == .APPLY_SELECTOR do return none
  let some selector := (← read).userNames[key term[0]!]?
    | throwError "unmapped datatype selector: {term[0]!}"
  return mkApp selector (← Smt.Reconstruct.reconstructTerm term[1]!)

end Smt2Lean.Selectors
