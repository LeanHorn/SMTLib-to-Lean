import Lean
import Smt2Lean.Source

namespace Smt2Lean

/-- A closed, checked clause or assertion definition, with its original location. -/
structure StatementPart where
  name : Lean.Name
  value : Lean.Expr
  source : Option Source.Ref := none
  label : String

/-- A checked query and the named definitions used to assemble it. -/
structure Statement where
  value : Lean.Expr
  parts : Array StatementPart := #[]
  definitions : Array StatementPart := #[]
  deriving Inhabited

end Smt2Lean
