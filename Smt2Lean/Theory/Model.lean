import Smt2Lean.Theory.Array
import Smt2Lean.Theory.Selector

namespace Smt2Lean.Models

open Lean Meta Backend

private inductive Dependency where
  | array (sort : cvc5.Sort)
  | datatype (index : Nat)
  deriving BEq

/-- Arrays and datatype fields can depend on each other, but nested recursive
datatypes have already been rejected by the backend. -/
private partial def dependencies (groups : Array Datatypes.CompiledGroup)
    (sort : cvc5.Sort) (active : Array Dependency := #[])
    : StateT (Array Dependency) MetaM Unit := do
  let node ← if sort.isArray then pure (Dependency.array sort)
    else if let some i := groups.findIdx? (fun g => g.source.types.any (·.sort == sort)) then
      pure (.datatype i)
    else return
  if (← get).contains node then return
  if active.contains node then throwError "cyclic array/datatype dependency"
  let active := active.push node
  match node with
  | .array sort =>
    dependencies groups sort.getArrayIndexSort! active
    dependencies groups sort.getArrayElementSort! active
  | .datatype i =>
    for field in groups[i]!.parameters do dependencies groups field active
  modify (·.push node)

/-- Bind array models and instantiate checked inductives in field-dependency order. -/
def withModels [Inhabited α] (datatypes : Array DatatypeGroup) (terms : Array cvc5.Term)
    (cache : Std.HashMap cvc5.Sort Expr) (context : Smt.Reconstruct.Context)
    (inspect : Array Expr → Array Expr → Std.HashMap cvc5.Sort Expr →
      Smt.Reconstruct.Context → MetaM α)
    (constructors : Array ArrayConstructor := #[]) : MetaM α := do
  let groups ← datatypes.mapM Datatypes.compile
  let (arrays, constants) := Arrays.collectSorts terms constructors
  let roots := arrays ++ datatypes.flatMap (fun group => group.types.map (·.sort))
  let (_, order) ← (roots.forM fun sort => dependencies groups sort).run #[]
  go groups constants order.toList #[] #[] cache context
where
  go (groups : Array Datatypes.CompiledGroup) (constants : Array cvc5.Sort)
      (order : List Dependency) (parameters laws : Array Expr)
      (cache : Std.HashMap cvc5.Sort Expr) (context : Smt.Reconstruct.Context) : MetaM α := do
    match order with
    | [] => Selectors.withInterpretations groups terms cache context fun choices context =>
        inspect (parameters ++ choices) laws cache context
    | .datatype i :: rest =>
      let (cache, context) ← Datatypes.bind groups[i]! cache context
      go groups constants rest parameters laws cache context
    | .array sort :: rest =>
      Arrays.withModels #[sort] constants cache context (constructors := constructors) fun ps ls cache context =>
        go groups constants rest (parameters ++ ps) (laws ++ ls) cache context

end Smt2Lean.Models
