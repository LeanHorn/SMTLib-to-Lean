import cvc5
import Smt2Lean.Source

namespace Smt2Lean.Backend

/-- A checked definition, with earlier definitions already expanded in its body. -/
structure ParsedDefinition where
  symbol : cvc5.Term
  parameters : Array cvc5.Term
  body : cvc5.Term
  source : Source.Ref

/-- SMT mode rejects HORN; CHC and auto modes accept it. Clause validation is separate. -/
inductive ParseMode where
  | smt
  | chc
  | auto
  deriving BEq

/-- An SMT name and its native identity. No Lean name has been assigned yet. -/
structure ParsedDeclaration where
  name : String
  term : cvc5.Term
  source : Option Source.Ref := none

/-- A nullary uninterpreted sort, identified independently of its spelling. -/
structure ParsedSort where
  name : String
  sort : cvc5.Sort
  source : Option Source.Ref := none

/-- One validated query. Use native terms only inside `inspect`. -/
structure ParsedQuery where
  number : Nat := 1
  logic : Option String := none
  checkCommand : String := "check-sat"
  assumptionCount : Nat := 0
  source : Option Source.Ref := none
  commands : Array Source.Command := #[]
  sorts : Array ParsedSort := #[]
  declarations : Array ParsedDeclaration := #[]
  definitions : Array ParsedDefinition := #[]
  assertions : Array cvc5.Term := #[]
  assertionSources : Array Source.Ref := #[]
  invoked : Array String := #[]

end Smt2Lean.Backend
