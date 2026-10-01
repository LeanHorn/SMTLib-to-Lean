import Smt2Lean.Backend.Types

namespace Smt2Lean.Backend

/-- Supported first-order value sorts, including recursively nested arrays. -/
partial def isValueSort (sort : cvc5.Sort) (sorts : Array ParsedSort := #[]) : Bool :=
  sort.isBoolean || sort.isInteger || sort.isReal ||
    (sort.isBitVector && sort.getBitVectorSize! != 0) || sorts.any (·.sort == sort) ||
    (sort.isArray && isValueSort sort.getArrayIndexSort! sorts &&
      isValueSort sort.getArrayElementSort! sorts)

/-- Reject indices that cvc5 would silently saturate before we can inspect its AST. -/
def validateBitvectorIndices (tokens : Array String) : cvc5.Env Unit := do
  for i in [:tokens.size] do
    unless tokens[i]? == some "(" && tokens[i + 1]? == some "_" do continue
    let op := tokens[i + 2]?.getD ""
    let label := if #["rotate_left", "rotate_right", "|rotate_left|", "|rotate_right|"].contains op then
        some "rotation index"
      else if #["int_to_bv", "int2bv", "|int_to_bv|", "|int2bv|"].contains op then
        some "conversion width"
      else none
    let some label := label | continue
    if let some amount := (tokens[i + 3]?.getD "").toNat? then
      if amount > 4294967295 then
        throw (.unsupported s!"{label} exceeds the native parser limit 4294967295")

/-- First-order functions over supported scalar and array sorts. -/
def isSupportedFunction (sort : cvc5.Sort) (sorts : Array ParsedSort := #[]) : cvc5.Env Bool := do
  unless sort.isFunction do return false
  let domains ← ofExcept sort.getFunctionDomainSorts
  let result ← ofExcept sort.getFunctionCodomainSort
  return !domains.isEmpty && domains.all (isValueSort · sorts) && isValueSort result sorts

/-- Check sorts, operators, declarations, and bound-variable scope. -/
def validateTerm (root : cvc5.Term)
    (declarations : Array ParsedDeclaration) (allowQuantifiers : Bool)
    (bound : Array cvc5.Term := #[]) (sorts : Array ParsedSort := #[])
    (constructors : Array ArrayConstructor := #[]) : cvc5.Env Unit := do
  for binder in bound do
    unless (← ofExcept binder.getKind) == .VARIABLE &&
        isValueSort (← ofExcept binder.getSort) sorts do
      throw (.unsupported "definition parameters must have a supported value sort")
  let mut pending : Array (cvc5.Term × Array cvc5.Term) := #[(root, bound)]
  let mut visited : Std.HashSet (cvc5.Term × Array cvc5.Term) := {}
  while !pending.isEmpty do
    let (term, bound) := pending.back!
    pending := pending.pop
    -- A shared term must be checked again when its scope changes.
    if visited.contains (term, bound) then continue
    visited := visited.insert (term, bound)
    let sort ← ofExcept term.getSort
    unless isValueSort sort sorts do
      throw (.unsupported s!"unsupported value sort: {sort}")
    let kind ← ofExcept term.getKind
    let children := term.getChildren
    if kind == .APPLY_SELECTOR then
      unless children.size == 2 && children[1]!.getSort!.isDatatype &&
          isValueSort children[1]!.getSort! sorts do
        throw (.unsupported "expected a datatype selector and one datatype argument")
      let datatype ← ofExcept children[1]!.getSort!.getDatatype
      let mut found := false
      for constructor in datatype do
        for h : i in [:constructor.getNumSelectors] do
          if (← constructor[i].getTerm) == children[0]! then
            unless sort == (← constructor[i].getCodomainSort) do
              throw (.unsupported "wrong datatype selector result sort")
            found := true
      unless found do throw (.unsupported "unmapped datatype selector")
      pending := pending.push (children[1]!, bound)
      continue
    if kind == .APPLY_CONSTRUCTOR then
      unless sort.isDatatype && !children.isEmpty do
        throw (.unsupported "expected a datatype constructor application")
      let datatype ← ofExcept sort.getDatatype
      let mut found := false
      for constructor in datatype do
        if (← constructor.getTerm) == children[0]! then
          unless children.size == constructor.getNumSelectors + 1 do
            throw (.unsupported "wrong datatype constructor arity")
          for h : i in [:constructor.getNumSelectors] do
            unless children[i + 1]!.getSort! == (← constructor[i].getCodomainSort) do
              throw (.unsupported "wrong datatype constructor field sort")
          found := true
      unless found do throw (.unsupported "unmapped datatype constructor")
      pending := pending ++ (children.extract 1 children.size).map (·, bound)
      continue
    if constructors.any (·.matches term) then
      unless children[2]!.getSort! == sort.getArrayElementSort! do
        throw (.unsupported "constant-array payload has the wrong element sort")
      pending := pending.push (children[2]!, bound)
      continue
    if kind == .CONST_ARRAY then
      unless sort.isArray && term.isConstArray && children.isEmpty do
        throw (.unsupported "expected a native constant-array value")
      let base ← ofExcept term.getConstArrayBase
      unless base.getSort! == sort.getArrayElementSort! do
        throw (.unsupported "constant-array value has the wrong element sort")
      -- Native constant-array values have no ordinary children.
      pending := pending.push (base, bound)
      continue
    if kind == .FORALL || kind == .EXISTS then
      unless allowQuantifiers do
        throw (.unsupported "quantifiers require a quantified logic or ALL")
      unless children.size == 2 do
        throw (.unsupported "expected a quantifier without annotations")
      let variables := children[0]!
      unless (← ofExcept variables.getKind) == .VARIABLE_LIST &&
          !variables.getChildren.isEmpty do
        throw (.unsupported "expected a nonempty quantifier variable list")
      let mut scope := bound
      for binder in variables.getChildren do
        unless (← ofExcept binder.getKind) == .VARIABLE do
          throw (.unsupported "expected a bound variable")
        let variableSort ← ofExcept binder.getSort
        unless isValueSort variableSort sorts do
          throw (.unsupported s!"unsupported bound variable sort: {variableSort}")
        scope := scope.push binder
      pending := pending.push (children[1]!, scope)
      continue
    if kind == .APPLY_UF then
      let some function := children[0]?
        | throw (.unsupported "function application has no function")
      unless declarations.any (·.term == function) do
        throw (.unsupported s!"undeclared term: {function}")
      let signature ← ofExcept function.getSort
      unless ← isSupportedFunction signature sorts do
        throw (.unsupported s!"unsupported function signature: {signature}")
      let domains ← ofExcept signature.getFunctionDomainSorts
      let arguments := children.extract 1 children.size
      unless arguments.size == domains.size do
        throw (.unsupported s!"wrong argument count for {function}: expected {domains.size}, got {arguments.size}")
      for argument in arguments, domain in domains do
        unless (← ofExcept argument.getSort) == domain do
          throw (.unsupported s!"wrong argument sort for {function}: expected {domain}")
      unless sort == (← ofExcept signature.getFunctionCodomainSort) do
        throw (.unsupported s!"wrong result sort for {function}")
      -- Validate the arguments; the declared function is allowed only as the head.
      pending := pending ++ arguments.map (·, bound)
      continue
    let validArity ← match kind with
      | .CONST_BOOLEAN | .CONST_INTEGER | .CONST_RATIONAL | .CONST_BITVECTOR => pure children.isEmpty
      | .CONSTANT => do
        unless declarations.any (·.term == term) do
          throw (.unsupported s!"undeclared term: {term}")
        pure children.isEmpty
      | .VARIABLE => do
        unless bound.contains term do
          throw (.unsupported s!"unbound variable: {term}")
        pure children.isEmpty
      | .NOT | .NEG | .ABS | .TO_INTEGER | .IS_INTEGER => pure (children.size == 1)
      | .BITVECTOR_NEG | .BITVECTOR_NOT | .BITVECTOR_EXTRACT | .BITVECTOR_REPEAT
      | .BITVECTOR_ZERO_EXTEND | .BITVECTOR_SIGN_EXTEND
      | .INT_TO_BITVECTOR | .BITVECTOR_UBV_TO_INT | .BITVECTOR_SBV_TO_INT | .BITVECTOR_NEGO
      | .BITVECTOR_ROTATE_LEFT | .BITVECTOR_ROTATE_RIGHT => pure (children.size == 1)
      | .TO_REAL => do
        -- cvc5 also accepts Real here; SMT-LIB specifies an Int argument.
        unless children.size == 1 && children[0]!.getSort!.isInteger do
          throw (.unsupported "to_real expects one Int argument")
        pure true
      | .ITE => pure (children.size == 3)
      | .SELECT => do
        unless children.size == 2 && children[0]!.getSort!.isArray &&
            children[1]!.getSort! == children[0]!.getSort!.getArrayIndexSort! &&
            sort == children[0]!.getSort!.getArrayElementSort! do
          throw (.unsupported "select expects an array and an index of its index sort")
        pure true
      | .STORE => do
        unless children.size == 3 && sort.isArray && children[0]!.getSort! == sort &&
            children[1]!.getSort! == sort.getArrayIndexSort! &&
            children[2]!.getSort! == sort.getArrayElementSort! do
          throw (.unsupported "store expects an array, an index, and an element of matching sorts")
        pure true
      | .AND | .OR | .XOR | .IMPLIES | .DISTINCT | .ADD | .SUB | .MULT | .INTS_DIVISION | .DIVISION =>
        pure (children.size >= 2)
      | .BITVECTOR_ADD | .BITVECTOR_MULT | .BITVECTOR_AND | .BITVECTOR_OR | .BITVECTOR_XOR
      | .BITVECTOR_CONCAT =>
        pure (children.size >= 2)
      | .BITVECTOR_SUB | .BITVECTOR_NAND | .BITVECTOR_NOR | .BITVECTOR_XNOR | .BITVECTOR_COMP
      | .BITVECTOR_SHL | .BITVECTOR_LSHR | .BITVECTOR_ASHR
      | .BITVECTOR_UDIV | .BITVECTOR_UREM | .BITVECTOR_SDIV | .BITVECTOR_SREM | .BITVECTOR_SMOD
      | .BITVECTOR_UADDO | .BITVECTOR_SADDO | .BITVECTOR_UMULO | .BITVECTOR_SMULO
      | .BITVECTOR_ULT | .BITVECTOR_ULE | .BITVECTOR_UGT | .BITVECTOR_UGE
      | .BITVECTOR_SLT | .BITVECTOR_SLE | .BITVECTOR_SGT | .BITVECTOR_SGE =>
        pure (children.size == 2)
      -- cvc5 expands chains into conjunctions of adjacent binary comparisons.
      | .EQUAL | .LT | .LEQ | .GT | .GEQ | .INTS_MODULUS => pure (children.size == 2)
      | _ => throw (.unsupported s!"unsupported operator: {kind}")
    unless validArity do
      throw (.unsupported s!"unsupported arity for {kind}: {children.size}")
    pending := pending ++ children.map (·, bound)

/-- Assertions must be Boolean and contain only the supported, scoped terms. -/
def validateAssertion (root : cvc5.Term)
    (declarations : Array ParsedDeclaration) (allowQuantifiers : Bool := true)
    (sorts : Array ParsedSort := #[]) (constructors : Array ArrayConstructor := #[]) : cvc5.Env Unit := do
  unless (← ofExcept root.getSort).isBoolean do
    throw (.unsupported "expected a Bool assertion")
  validateTerm root declarations allowQuantifiers (sorts := sorts) (constructors := constructors)

def knownTerms (query : ParsedQuery) : Array ParsedDeclaration :=
  query.declarations ++ query.definitions.map fun d =>
    { name := d.symbol.toString, term := d.symbol, source := some d.source }

/-- All native roots needed to bind array models, including erased constant-array constructors. -/
def arrayModelTerms (query : ParsedQuery) : Array cvc5.Term :=
  query.declarations.map (·.term) ++ query.assertionTerms ++ query.assertions.flatMap (·.arrayConstants) ++
    query.namedArrayConstants.flatMap (·.2) ++
    query.definitions.flatMap (fun d => #[d.symbol, d.body] ++ d.parameters ++ d.arrayConstants)

/-- Recognize canonical sort syntax, including aliases with formal parameters. -/
private partial def sortSyntax (names : Array String) : List String → Option (List String)
  | "(" :: "Array" :: rest => do
    let rest ← sortSyntax names rest
    let ")" :: rest ← sortSyntax names rest | none
    return rest
  | "(" :: "_" :: "BitVec" :: width :: ")" :: rest =>
    if width.toNat?.getD 0 > 0 then some rest else none
  | name :: rest => if names.contains name then some rest else none
  | _ => none

/-- Check the resolved alias body; cvc5 handles syntax, arity, scope, and substitution. -/
def validateSortAlias (command : cvc5.Command) (sorts : Array ParsedSort := #[]) : cvc5.Env Unit := do
  let tokens := Source.tokenize command.toString
  let some endParams := (tokens.extract 4 tokens.size).findIdx? (· == ")")
    | throw (.unsupported s!"unsupported sort alias: {command}")
  let endParams := endParams + 4
  let body := tokens.extract (endParams + 1) (tokens.size - 1)
  let names := #["Bool", "Int", "Real"] ++ sorts.map (·.sort.toString) ++ tokens.extract 4 endParams
  unless tokens[0]? == some "(" && tokens[1]? == some "define-sort" &&
      tokens[3]? == some "(" && tokens.back? == some ")" &&
      sortSyntax names body.toList == some [] do
    throw (.unsupported s!"unsupported sort alias: {command}; expected a supported value sort or sort parameter")

/-- These metadata fields never become assumptions or select a proof target. -/
def validateMetadata (command : cvc5.Command) : cvc5.Env Unit := do
  -- The binding exposes no command arguments; inspect cvc5's canonical printing.
  let text := command.toString
  let keys := #[":status", ":source", ":category", ":license", ":notes"]
  if keys.any (fun key => text.startsWith s!"(set-info {key} ") then return
  if text == "(set-info :smt-lib-version 2.6)" then return
  throw (.unsupported s!"unsupported metadata: {text}")

/-- Validate solver controls without applying them. Native parsing alone does not check values. -/
def validateSolverOption (command : cvc5.Command) : cvc5.Env Unit := do
  let text := command.toString
  for key in #[":produce-models", ":produce-proofs", ":produce-unsat-cores", ":print-success"] do
    if text.startsWith s!"(set-option {key} " then
      unless text == s!"(set-option {key} true)" || text == s!"(set-option {key} false)" do
        throw (.error s!"invalid value for {key}: expected true or false")
      return
  let seedPrefix := "(set-option :random-seed "
  if text.startsWith seedPrefix then
    let value := ((text.drop seedPrefix.length).dropEnd 1).toString
    -- SMT-LIB numerals are 0 or a nonzero digit followed by digits. No size limit.
    unless !value.isEmpty && value.toList.all Char.isDigit &&
        (value == "0" || !value.startsWith "0") do
      throw (.error "invalid value for :random-seed: expected an SMT-LIB numeral")
    return
  throw (.unsupported s!"unsupported solver option: {text}")

/-- Add a location without changing the native error category. -/
def errorWithContext (context : String) : cvc5.Error → cvc5.Error
  | .error message => .error s!"{context}: {message}"
  | .recoverable message => .recoverable s!"{context}: {message}"
  | .unsupported message => .unsupported s!"{context}: {message}"
  | .option message => .option s!"{context}: {message}"
  | .missingValue => .error s!"{context}: missing native value"

end Smt2Lean.Backend
