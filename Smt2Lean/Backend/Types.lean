import cvc5
import Smt2Lean.Source

namespace Smt2Lean.Backend

/-- A checked definition, with earlier definitions already expanded in its body. -/
structure ParsedDefinition where
  symbol : cvc5.Term
  parameters : Array cvc5.Term
  body : cvc5.Term
  source : Source.Ref
  /-- Native roots retaining constant-array requirements, including discarded subterms. -/
  arrayConstants : Array cvc5.Term := #[]

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

/-- A declared value sort, identified independently of its spelling. -/
structure ParsedSort where
  name : String
  sort : cvc5.Sort
  source : Option Source.Ref := none
  deriving Inhabited

/-- A constructor field with its native selector identity and result sort. -/
structure DatatypeField where
  name : String
  selector : cvc5.Term
  sort : cvc5.Sort
  deriving Inhabited

structure DatatypeConstructor where
  name : String
  term : cvc5.Term
  fields : Array DatatypeField
  deriving Inhabited

structure ParsedDatatype extends ParsedSort where
  constructors : Array DatatypeConstructor
  deriving Inhabited

/-- One native declaration group; recursion is allowed only through direct fields. -/
structure DatatypeGroup where
  types : Array ParsedDatatype
  source : Source.Ref
  deriving Inhabited

/-- A private, typed store used only to carry a constant-array payload through cvc5. -/
structure ArrayConstructor where
  base : cvc5.Term
  index : cvc5.Term
  deriving Inhabited

def ArrayConstructor.matches (constructor : ArrayConstructor) (term : cvc5.Term) : Bool :=
  term.getKind! == .STORE && term.getNumChildren == 3 &&
    term[0]! == constructor.base && term[1]! == constructor.index

/-- An assertion and the metadata that must follow its scope. -/
structure ParsedAssertion where
  term : cvc5.Term
  source : Source.Ref
  arrayConstants : Array cvc5.Term := #[]
  deriving Inhabited

/-- One validated query. Use native terms only inside `inspect`. -/
structure ParsedQuery where
  number : Nat := 1
  logic : Option String := none
  checkCommand : String := "check-sat"
  assumptionCount : Nat := 0
  source : Option Source.Ref := none
  commands : Array Source.Command := #[]
  sorts : Array ParsedSort := #[]
  datatypes : Array DatatypeGroup := #[]
  declarations : Array ParsedDeclaration := #[]
  definitions : Array ParsedDefinition := #[]
  assertions : Array ParsedAssertion := #[]
  /-- Private parser carriers, recognized by native identity rather than spelling. -/
  arrayConstructors : Array ArrayConstructor := #[]
  /-- Theory requirements of named terms follow their declaration scopes. -/
  namedArrayConstants : Array (String × Array cvc5.Term) := #[]
  /-- Invoked source commands; private parser declarations are excluded. -/
  invoked : Array String := #[]

def ParsedQuery.assertionTerms (query : ParsedQuery) : Array cvc5.Term :=
  query.assertions.map (·.term)

/-- All declared value sorts; only `sorts` are arbitrary uninterpreted carriers. -/
def ParsedQuery.valueSorts (query : ParsedQuery) : Array ParsedSort :=
  query.sorts ++ query.datatypes.flatMap (fun group => group.types.map (·.toParsedSort))

def ParsedQuery.assertionSources (query : ParsedQuery) : Array Source.Ref :=
  query.assertions.map (·.source)

end Smt2Lean.Backend
