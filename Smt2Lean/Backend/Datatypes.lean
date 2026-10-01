import Smt2Lean.Backend.Validate

namespace Smt2Lean.Backend

/-- Datatypes are absent from SymbolManager.getDeclaredSorts. Resolve a qualified
constructor from each native, canonically printed declaration instead. -/
def datatypeSorts (command : cvc5.Command) (solver : cvc5.Solver)
    (symbols : cvc5.SymbolManager) : cvc5.Env (Array cvc5.Sort) := do
  let tokens := Source.tokenize command.toString
  let mut names := #[]
  let mut i := 3
  while tokens[i]? == some "(" do
    unless tokens[i + 2]? == some "0" && tokens[i + 3]? == some ")" do
      throw (.unsupported "parametric datatypes are not supported")
    names := names.push tokens[i + 1]!
    i := i + 4
  unless tokens[i]? == some ")" && tokens[i + 1]? == some "(" do
    throw (.unsupported "expected monomorphic datatype declarations")
  i := i + 2
  let parser ← cvc5.InputParser.new solver (some symbols)
  let mut sorts := #[]
  for name in names do
    unless tokens[i]? == some "(" && tokens[i + 1]? == some "(" do
      throw (.unsupported "expected a nonempty monomorphic constructor list")
    parser.setStringInput s!"(as {tokens[i + 2]!} {name})"
    let term ← parser.nextTerm
    let sort ← ofExcept term.getSort
    let sort ← if sort.isDatatypeConstructor then ofExcept sort.getDatatypeConstructorCodomainSort
      else pure sort
    sorts := sorts.push sort
    let mut depth := 1
    i := i + 1
    while depth != 0 do
      let some token := tokens[i]? | throw (.error "incomplete native datatype declaration")
      if token == "(" then depth := depth + 1
      if token == ")" then depth := depth - 1
      i := i + 1
  return sorts

private partial def containsSort (sort : cvc5.Sort) (group : Array cvc5.Sort) : Bool :=
  group.contains sort || (sort.isArray &&
    (containsSort sort.getArrayIndexSort! group || containsSort sort.getArrayElementSort! group))

/-- Read checked native declarations, without interpreting constructors as user functions. -/
def readDatatypes (sorts : Array cvc5.Sort) (query : ParsedQuery) (source : Source.Ref)
    : cvc5.Env DatatypeGroup := do
  if sorts.isEmpty then throw (.error "expected a new datatype declaration")
  let mut types := #[]
  for sort in sorts do
    unless sort.isDatatype do throw (.unsupported "expected a datatype sort")
    let datatype ← ofExcept sort.getDatatype
    if datatype.isParametric then throw (.unsupported "parametric datatypes are not supported")
    if datatype.isCodatatype || !datatype.isWellFounded then
      throw (.unsupported "expected a well-founded inductive datatype")
    let mut constructors := #[]
    for constructor in datatype do
      let mut fields := #[]
      for selector in constructor do
        fields := fields.push {
          name := ← ofExcept selector.getName
          selector := ← selector.getTerm
          sort := ← selector.getCodomainSort }
      constructors := constructors.push {
        name := ← ofExcept constructor.getName, term := ← constructor.getTerm, fields }
    types := types.push {
      name := ← ofExcept datatype.getName, sort, source := some source, constructors }
  let known := query.valueSorts ++ types.map (·.toParsedSort)
  for datatype in types do
    for constructor in datatype.constructors do
      for field in constructor.fields do
        unless isValueSort field.sort known do
          throw (.unsupported s!"unsupported datatype field sort: {field.sort}")
        if !sorts.contains field.sort && containsSort field.sort sorts then
          throw (.unsupported "nested datatype recursion is not supported; use direct recursive fields")
  return { types, source }

end Smt2Lean.Backend
