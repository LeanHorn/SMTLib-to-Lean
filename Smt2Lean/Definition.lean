import Lean
import Smt2Lean.Source

namespace Smt2Lean

/-- A closed, kernel-checked interpretation of an ordinary SMT `define-fun`.
The original SMT name is independent of Lean declaration names. `type` includes
every parameter, in source order, even unused parameters. SMT Bool becomes Prop.
No native parser objects or newly generated Lean declarations are retained.
This records a definition's meaning, not a proof that it satisfies any assertions. -/
structure ReconstructedDefinition where
  name : String
  type : Lean.Expr
  value : Lean.Expr
  source : Source.Ref
  deriving Inhabited

end Smt2Lean
