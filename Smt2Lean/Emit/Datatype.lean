import Lean.Meta

namespace Smt2Lean.Emit.Datatypes

open Lean Meta

def isGenerated (name : Name) : Bool := (`SMT.Datatypes).isPrefixOf name

/-- A nullary constructor can hide all evidence of its external field carriers.
Keep those arguments explicit so re-elaboration cannot lose their identities. -/
def showParameters (value : Expr) : CoreM Expr :=
  Core.transform value (post := fun expression => do
    if expression.isApp then
      let .const name _ := expression.getAppFn | return .done expression
      if isGenerated name then
        if let .ctorInfo info ← getConstInfo name then
          if info.numParams > 0 then return .done expression.setAppPPExplicit
    return .done expression)

/-- Find entire mutual groups, including types used only in constructor fields. -/
def groups (values : Array Expr) : MetaM (Array (Array Name)) := do
  let mut values := values
  for value in values do
    for name in value.getUsedConstants.filter ((`SMT.Selectors).isPrefixOf ·) do
      let helper ← getConstInfoDefn name
      values := values ++ #[helper.type, helper.value]
  let mut found : Array (Array Name) := #[]
  for value in values do
    for name in value.getUsedConstants.filter isGenerated do
      let info ← getConstInfo name
      let datatype ← match info with
        | .inductInfo info => pure info
        | .ctorInfo info => getConstInfoInduct info.induct
        | _ => continue
      let names := datatype.all.toArray
      unless found.contains names do found := found.push names
  return found.qsort (fun a b => Name.lt a[0]! b[0]!)

/-- Print the kernel-checked inductive signatures, not a separate source encoding. -/
def render (groups : Array (Array Name)) (printExpr : Expr → MetaM String) : MetaM String := do
  let mut result := ""
  for group in groups do
    if group.size > 1 then result := result ++ "mutual\n"
    for name in group do
      let info ← getConstInfoInduct name
      let text ← forallTelescope info.type fun parameters _ => do
        let binders ← parameters.mapM fun p =>
          return s!"({← printExpr p} : Type)"
        let parameterText := String.join (binders.toList.map (" " ++ ·))
        let mut text := s!"inductive {name}{parameterText} : Type where\n"
        for constructor in info.ctors do
          let ctor ← getConstInfoCtor constructor
          let type ← instantiateForall ctor.type parameters
          let fieldTypes ← forallTelescope type fun fields _ =>
            fields.mapM fun field => do printExpr (← inferType field)
          let fields := fieldTypes.mapIdx fun i type => s!"(field{i} : {type})"
          let shortName := Name.mkSimple constructor.getString!
          text := text ++ s!"  | {shortName}" ++ String.join (fields.toList.map (" " ++ ·)) ++ "\n"
        return text
      result := result ++ text
    if group.size > 1 then result := result ++ "end\n"
    result := result ++ "\n"
  return result

/-- Field types can require Real imports even if the proposition never mentions Real directly. -/
def usesReal (groups : Array (Array Name)) : MetaM Bool := do
  for group in groups do
    for name in group do
      for constructor in (← getConstInfoInduct name).ctors do
        if ((← getConstInfoCtor constructor).type.find? (·.isConstOf `Real)).isSome then return true
  return false

end Smt2Lean.Emit.Datatypes
