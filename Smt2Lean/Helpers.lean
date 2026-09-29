import Smt.Reconstruct.Builtin

namespace Smt2Lean.Helpers

open Lean Meta Qq

/-- Names reserved for the operator definitions copied into generated files. -/
def isHelper (name : Name) : Bool :=
  name == `SMT.xor || match name with
    | .str `SMT suffix => suffix.startsWith "distinct" &&
        (suffix.drop 8).toString.toNat?.isSome
    | _ => false

private def define (name : Name) (levels : List Name) (value : Expr) : MetaM Name := do
  unless (← getEnv).contains name do
    let declaration : Declaration := .defnDecl {
      name, levelParams := levels, type := ← inferType value, value
      hints := .abbrev, safety := .safe
    }
    let env ← ofExceptKernelException <| (← getEnv).addDeclCore 0 1000 declaration none
    setEnv env
  return name

def xor : MetaM Name :=
  define `SMT.xor [] q(fun (p q : Prop) => (p ∧ ¬q) ∨ (¬p ∧ q))

/-- One polymorphic helper per arity, sharing lean-smt's pairwise encoding. -/
def distinct (arity : Nat) : MetaM Name := do
  let name := Name.str `SMT s!"distinct{arity}"
  if (← getEnv).contains name then return name
  let u := Level.param `u
  withLocalDecl `α .implicit (.sort u) fun α => do
    withLocalDeclsDND (Array.ofFn (n := arity) fun i => (Name.mkSimple s!"x{i.val}", α)) fun xs => do
      let body := Smt.Reconstruct.Builtin.buildDistinct u α xs.toList
      define name [`u] (← mkLambdaFVars (#[α] ++ xs) body)

end Smt2Lean.Helpers
