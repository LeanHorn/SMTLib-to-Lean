import Smt2Lean.Helpers
import Smt2Lean.Backend.Types

namespace Smt2Lean.Arrays

open Lean Meta Qq

/-- Collect array sorts in dependency order, including unused function/binder sorts. -/
private partial def addSort (sort : cvc5.Sort) : StateM (Array cvc5.Sort) Unit := do
  if sort.isFunction then
    for domain in sort.getFunctionDomainSorts! do addSort domain
    addSort sort.getFunctionCodomainSort!
  else if sort.isArray && !(← get).contains sort then
    addSort sort.getArrayIndexSort!
    addSort sort.getArrayElementSort!
    modify (·.push sort)

private def collectSorts (terms : Array cvc5.Term)
    (constructors : Array Backend.ArrayConstructor) : Array cvc5.Sort × Array cvc5.Sort := Id.run do
  let mut sorts := #[]
  let mut constants := #[]
  let mut pending := terms.reverse
  let mut visited : Std.HashSet cvc5.Term := {}
  while !pending.isEmpty do
    let term := pending.back!
    pending := pending.pop
    if visited.contains term then continue
    visited := visited.insert term
    sorts := (addSort term.getSort!).run sorts |>.2
    pending := pending ++ term.getChildren.reverse
    if constructors.any (fun c => c.base == term || c.matches term) then
      unless constants.contains term.getSort! do constants := constants.push term.getSort!
    if term.isConstArray then
      unless constants.contains term.getSort! do constants := constants.push term.getSort!
      pending := pending.push term.getConstArrayBase!
  return (sorts, constants)

/-- Keys use fresh Lean carrier identities, never source spellings. -/
private def operationKey (carrier : Expr) (operation : String) : String :=
  s!"SMT.array.{carrier.fvarId!.name}.{operation}"

private def constructorKey (base : cvc5.Term) : String :=
  s!"SMT.constArray.{base.getId!}"

/-- Introduce carriers and operations outside source binders, sharing each native sort's model. -/
def withModels [Inhabited α] (terms : Array cvc5.Term)
    (sortCache : Std.HashMap cvc5.Sort Expr) (context : Smt.Reconstruct.Context)
    (inspect : Array Expr → Array Expr → Std.HashMap cvc5.Sort Expr →
      Smt.Reconstruct.Context → MetaM α)
    (constructors : Array Backend.ArrayConstructor := #[]) : MetaM α := do
  let (sorts, constants) := collectSorts terms constructors
  go constants sorts.toList #[] #[] sortCache context
where
  go (constants : Array cvc5.Sort) (sorts : List cvc5.Sort) (parameters laws : Array Expr)
      (cache : Std.HashMap cvc5.Sort Expr) (context : Smt.Reconstruct.Context) : MetaM α := do
    match sorts with
    | [] => inspect parameters laws cache context
    | sort :: rest =>
      let (index, _) ← (Smt.Reconstruct.reconstructSort sort.getArrayIndexSort!).run context { sortCache := cache }
      let (element, _) ← (Smt.Reconstruct.reconstructSort sort.getArrayElementSort!).run context { sortCache := cache }
      withLocalDeclD (← mkFreshUserName `Array) q(Type) fun carrier => do
        let readType ← mkArrow carrier (← mkArrow index element)
        let writeType ← mkArrow carrier (← mkArrow index (← mkArrow element carrier))
        withLocalDeclsDND #[(← mkFreshUserName `select, readType),
            (← mkFreshUserName `store, writeType)] fun operations => do
          let read := operations[0]!
          let write := operations[1]!
          let law := mkAppN (mkConst (← Helpers.arrayLaws)) #[index, element, carrier, read, write]
          let userNames := context.userNames
            |>.insert (operationKey carrier "select") read
            |>.insert (operationKey carrier "store") write
          let context := { context with userNames }
          let parameters := parameters ++ #[carrier, read, write]
          let laws := laws.push law
          let cache := cache.insert sort carrier
          if constants.contains sort then
            withLocalDeclD (← mkFreshUserName `constArray) (← mkArrow element carrier) fun const => do
              let law := mkAppN (mkConst (← Helpers.constArrayLaw)) #[index, element, carrier, read, const]
              let mut userNames := context.userNames.insert (operationKey carrier "const") const
              for constructor in constructors do
                if constructor.base.getSort! == sort then
                  userNames := userNames.insert (constructorKey constructor.base) const
              let context := { context with userNames }
              go constants rest (parameters.push const) (laws.push law) cache context
          else
            go constants rest parameters laws cache context

/-- Reconstruct array operations only against an explicitly bound model. -/
def reconstruct : Smt.TermReconstructor := fun term => do
  let kind ← ofExcept term.getKind
  unless kind == .SELECT || kind == .STORE || kind == .CONST_ARRAY do return none
  if kind == .STORE then
    if let some function := (← read).userNames[constructorKey term[0]!]? then
      return mkApp function (← Smt.Reconstruct.reconstructTerm term[2]!)
  let sort ← ofExcept (if kind == .CONST_ARRAY then term.getSort else term[0]!.getSort)
  let some carrier := (← get).sortCache[sort]?
    | throwError "missing array carrier for {sort}"
  let operation := if kind == .SELECT then "select" else if kind == .STORE then "store" else "const"
  let some function := (← read).userNames[operationKey carrier operation]?
    | throwError "missing array operation: {operation}"
  let children ← if kind == .CONST_ARRAY then do pure #[← ofExcept term.getConstArrayBase]
    else pure term.getChildren
  return mkAppN function (← children.mapM Smt.Reconstruct.reconstructTerm)

end Smt2Lean.Arrays
