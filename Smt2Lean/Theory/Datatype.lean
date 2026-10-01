import Smt2Lean.Backend.Types
import Smt2Lean.Theory.BitVec
import Smt2Lean.Theory.Helpers
import Lean.Meta.Constructions.CasesOn

namespace Smt2Lean.Datatypes

open Lean Meta Qq Backend

/-- A checked inductive group, parameterized by its external interpretation carriers. -/
structure CompiledGroup where
  source : DatatypeGroup
  parameters : Array cvc5.Sort
  names : Array Name
  deriving Inhabited

def namePart (name : String) : String :=
  String.ofList <| name.toList.map fun c =>
    if ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || c.isDigit || c == '_' then c else '_'

private def constructorName (type : Name) (index : Nat) (name : String) : Name :=
  type.str s!"c{index}_{namePart name}"

private def constructorKey (term : cvc5.Term) : String :=
  s!"SMT.datatype.{term.getId!}"

private def testerKey (term : cvc5.Term) : String := s!"SMT.tester.{term.getId!}"

def getConstructor (term : cvc5.Term) : Smt.ReconstructM Expr := do
  let some value := (← read).userNames[constructorKey term]?
    | throwError "unmapped datatype constructor: {term}"
  return value

def getTesterConstructor (term : cvc5.Term) : Smt.ReconstructM Expr := do
  let some value := (← read).userNames[testerKey term]?
    | throwError "unmapped datatype tester: {term}"
  return value

/-- Keep unused case fields anonymous in emitted functions. -/
def anonymousUnused : Expr → Expr
  | .lam name type body info =>
    .lam (if body.hasLooseBVar 0 then name else `_) type (anonymousUnused body) info
  | value => value

/-- Build case analysis using a synchronously kernel-checked eliminator. -/
def casesOn (input result : Expr) (branches : Array Expr) : MetaM Expr := do
  let domain ← inferType input
  let typeName := domain.getAppFn.constName!
  let name := mkCasesOnName typeName
  unless (← getEnv).contains name do
    let declaration ← ofExceptKernelException (mkCasesOnImp (← getEnv).toKernelEnv typeName)
    let env ← ofExceptKernelException <| (← getEnv).addDeclCore 0 1000 declaration none
    setEnv (markAuxRecursor env name)
  let motive ← withLocalDeclD `_ domain fun x => mkLambdaFVars #[x] result (usedOnly := false)
  return mkAppN (mkConst name [← getLevel result])
    (domain.getAppArgs ++ #[motive, input] ++ branches)

private def externalSort (sort : cvc5.Sort) : Bool :=
  sort.isUninterpretedSort || sort.isArray || sort.isDatatype

private def implicitParameters : Nat → Expr → Expr
  | 0, type => type
  | n + 1, .forallE name domain body _ =>
    .forallE name domain (implicitParameters n body) .implicit
  | _, type => type

/-- Check a finite constructor witness for each type under nonempty field carriers. -/
private def checkNonempty (group : CompiledGroup) (parameters : Array Expr)
    (fieldType : cvc5.Sort → MetaM Expr) : MetaM Unit := do
  let assumptions ← parameters.mapIdxM fun i parameter =>
    return (Name.mkSimple s!"h{i}", ← mkAppM ``Nonempty #[parameter])
  withLocalDeclsDND assumptions fun hypotheses => do
    let mut witnesses : Array (Option Expr) := Array.replicate group.names.size none
    for _ in [:group.names.size] do
      for h : i in [:group.source.types.size] do
        if witnesses[i]!.isSome then continue
        for h : j in [:group.source.types[i].constructors.size] do
          let constructor := group.source.types[i].constructors[j]
          let mut arguments := #[]
          let mut ready := true
          for field in constructor.fields do
            if let some j := group.source.types.findIdx? (·.sort == field.sort) then
              if let some value := witnesses[j]! then arguments := arguments.push value
              else ready := false
            else if let some j := group.parameters.findIdx? (· == field.sort) then
              arguments := arguments.push (← mkAppM ``Classical.choice #[hypotheses[j]!])
            else
              let type ← fieldType field.sort
              arguments := arguments.push (← mkAppM ``Classical.choice #[
                ← synthInstance (← mkAppM ``Nonempty #[type])])
          if ready then
            let value := mkAppN (mkAppN (mkConst (constructorName group.names[i]! j constructor.name)) parameters) arguments
            witnesses := witnesses.set! i (some value)
            break
    for witness in witnesses do
      let some witness := witness | throwError "datatype has no finite constructor witness"
      let proof ← mkAppM ``Nonempty.intro #[witness]
      checkWithKernel (← mkLambdaFVars (parameters ++ hypotheses) proof)

/-- Build actual Lean inductives; constructor laws follow from the kernel declaration. -/
def compile (source : DatatypeGroup) : MetaM CompiledGroup := do
  let mut parameters := #[]
  for datatype in source.types do
    for constructor in datatype.constructors do
      for field in constructor.fields do
        if externalSort field.sort && !source.types.any (·.sort == field.sort) &&
            !parameters.contains field.sort then
          parameters := parameters.push field.sort
  let mut serial := 0
  let env ← getEnv
  while (source.types.mapIdx fun i datatype =>
      (`SMT.Datatypes).str s!"g{serial}" |>.str s!"T{i}_{namePart datatype.name}").any env.contains do
    serial := serial + 1
  let stem := (`SMT.Datatypes).str s!"g{serial}"
  -- Indices disambiguate sanitized source names and avoid Lean's reserved names.
  let names := source.types.mapIdx fun i datatype => stem.str s!"T{i}_{namePart datatype.name}"
  let group : CompiledGroup := { source, parameters, names }
  withLocalDeclsDND (parameters.mapIdx fun i _ => (Name.mkSimple s!"Field{i}", q(Type))) fun locals => do
    let fieldType := fun sort => do
      if let some i := source.types.findIdx? (·.sort == sort) then
        return mkAppN (mkConst names[i]!) locals
      if let some i := parameters.findIdx? (· == sort) then return locals[i]!
      return (← (Smt.Reconstruct.reconstructSort sort).run {} {}).1
    let types ← source.types.mapIdxM fun i datatype => do
      let ctors ← datatype.constructors.mapIdxM fun j constructor => do
        let fields ← constructor.fields.mapM (fun field => fieldType field.sort)
        let result := mkAppN (mkConst names[i]!) locals
        let type ← fields.foldrM (fun field body => do mkArrow field body) result
        let ctorName := constructorName names[i]! j constructor.name
        let ctorType ← mkForallFVars locals type
        return ({ name := ctorName, type := implicitParameters locals.size ctorType } : Lean.Constructor)
      return { name := names[i]!, type := ← mkForallFVars locals q(Type), ctors := ctors.toList : InductiveType }
    let declaration := Declaration.inductDecl [] locals.size types.toList false
    let env ← ofExceptKernelException <| (← getEnv).addDeclCore 0 1000 declaration none
    setEnv env
    checkNonempty group locals fieldType
  return group

/-- Instantiate a group only after every external field carrier has been bound. -/
def bind (group : CompiledGroup) (cache : Std.HashMap cvc5.Sort Expr)
    (context : Smt.Reconstruct.Context)
    : MetaM (Std.HashMap cvc5.Sort Expr × Smt.Reconstruct.Context) := do
  let parameters ← group.parameters.mapM fun sort => do
    let some type := cache[sort]? | throwError "missing datatype field carrier: {sort}"
    return type
  let mut cache := cache
  let mut context := context
  for datatype in group.source.types, name in group.names do
    cache := cache.insert datatype.sort (mkAppN (mkConst name) parameters)
    for h : j in [:datatype.constructors.size] do
      let constructor := datatype.constructors[j]
      let value := mkAppN (mkConst (constructorName name j constructor.name)) parameters
      let userNames := context.userNames
        |>.insert (constructorKey constructor.term) value
        |>.insert (testerKey constructor.tester) value
      context := { context with userNames }
  return (cache, context)

def reconstruct : Smt.TermReconstructor := fun term => do
  unless term.getKind! == .APPLY_CONSTRUCTOR do return none
  let constructor ← getConstructor term[0]!
  return mkAppN constructor (← (term.getChildren.extract 1 term.getNumChildren).mapM Smt.Reconstruct.reconstructTerm)

end Smt2Lean.Datatypes
