import Smt2Lean.Backend.Types

namespace Smt2Lean.Backend

def isScalarSort (sort : cvc5.Sort) (sorts : Array ParsedSort := #[]) : Bool :=
  sort.isBoolean || sort.isInteger || sort.isReal ||
    (sort.isBitVector && sort.getBitVectorSize! != 0) || sorts.any (·.sort == sort)

/-- cvc5 silently saturates oversized rotation indices; reject before native parsing. -/
def validateRotationIndices (tokens : Array String) : cvc5.Env Unit := do
  for i in [:tokens.size] do
    if tokens[i]? == some "(" && tokens[i + 1]? == some "_" &&
        #["rotate_left", "rotate_right", "|rotate_left|", "|rotate_right|"].contains
          (tokens[i + 2]?.getD "") then
      if let some amount := (tokens[i + 3]?.getD "").toNat? then
        if amount > 4294967295 then
          throw (.unsupported "rotation index exceeds the native parser limit 4294967295")

/-- cvc5 may retain signed integer numerals inside Real arithmetic. -/
def integerLiteral? (term : cvc5.Term) : Option Int := Id.run do
  let mut value := term
  let mut negative := false
  while value.getKind! == .NEG do
    negative := !negative
    value := value[0]!
  if !value.getSort!.isInteger || !value.isIntegerValue then return none
  let result := value.getIntegerValue!
  return some (if negative then -result else result)

/-- First-order functions over Bool, Int, Real, BitVec, and declared uninterpreted sorts. -/
def isSupportedFunction (sort : cvc5.Sort) (sorts : Array ParsedSort := #[]) : cvc5.Env Bool := do
  unless sort.isFunction do return false
  let domains ← ofExcept sort.getFunctionDomainSorts
  let result ← ofExcept sort.getFunctionCodomainSort
  return !domains.isEmpty && domains.all (isScalarSort · sorts) && isScalarSort result sorts

/-- Check sorts, operators, declarations, and bound-variable scope. -/
def validateTerm (root : cvc5.Term)
    (declarations : Array ParsedDeclaration) (allowQuantifiers : Bool)
    (bound : Array cvc5.Term := #[]) (sorts : Array ParsedSort := #[]) : cvc5.Env Unit := do
  for binder in bound do
    unless (← ofExcept binder.getKind) == .VARIABLE &&
        isScalarSort (← ofExcept binder.getSort) sorts do
      throw (.unsupported "definition parameters must have Bool, Int, Real, BitVec, or declared uninterpreted sorts")
  let mut pending : Array (cvc5.Term × Array cvc5.Term) := #[(root, bound)]
  let mut visited : Std.HashSet (cvc5.Term × Array cvc5.Term) := {}
  while !pending.isEmpty do
    let (term, bound) := pending.back!
    pending := pending.pop
    -- A shared term must be checked again when its scope changes.
    if visited.contains (term, bound) then continue
    visited := visited.insert (term, bound)
    let sort ← ofExcept term.getSort
    unless isScalarSort sort sorts do
      throw (.unsupported s!"expected Bool, Int, Real, BitVec, or a declared uninterpreted sort, got {sort}")
    let kind ← ofExcept term.getKind
    let children := term.getChildren
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
        unless isScalarSort variableSort sorts do
          throw (.unsupported s!"unsupported bound variable sort: {variableSort}; expected Bool, Int, Real, BitVec, or a declared uninterpreted sort")
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
      | .BITVECTOR_ROTATE_LEFT | .BITVECTOR_ROTATE_RIGHT => pure (children.size == 1)
      | .TO_REAL => do
        -- cvc5 also accepts Real here; SMT-LIB specifies an Int argument.
        unless children.size == 1 && children[0]!.getSort!.isInteger do
          throw (.unsupported "to_real expects one Int argument")
        pure true
      | .ITE => pure (children.size == 3)
      | .AND | .OR | .XOR | .IMPLIES | .DISTINCT | .ADD | .SUB | .MULT | .INTS_DIVISION | .DIVISION =>
        pure (children.size >= 2)
      | .BITVECTOR_ADD | .BITVECTOR_MULT | .BITVECTOR_AND | .BITVECTOR_OR | .BITVECTOR_XOR
      | .BITVECTOR_CONCAT =>
        pure (children.size >= 2)
      | .BITVECTOR_SUB | .BITVECTOR_NAND | .BITVECTOR_NOR | .BITVECTOR_XNOR | .BITVECTOR_COMP
      | .BITVECTOR_SHL | .BITVECTOR_LSHR | .BITVECTOR_ASHR
      | .BITVECTOR_UDIV | .BITVECTOR_UREM | .BITVECTOR_SDIV | .BITVECTOR_SREM | .BITVECTOR_SMOD
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
    (sorts : Array ParsedSort := #[]) : cvc5.Env Unit := do
  unless (← ofExcept root.getSort).isBoolean do
    throw (.unsupported "expected a Bool assertion")
  validateTerm root declarations allowQuantifiers (sorts := sorts)

def knownTerms (query : ParsedQuery) : Array ParsedDeclaration :=
  query.declarations ++ query.definitions.map fun d =>
    { name := d.symbol.toString, term := d.symbol, source := some d.source }

/--
cvc5 prints aliases with their bodies already resolved. A supported body is Bool,
Int, Real, a positive-width BitVec, a declared sort, or a formal parameter. Tokenize this
canonical header, respecting quoted names; cvc5 still handles alias syntax, arity, scope, and substitution.
-/
def validateSortAlias (command : cvc5.Command) (sorts : Array ParsedSort := #[]) : cvc5.Env Unit := do
  let tokens := Source.tokenize command.toString
  let some endParams := (tokens.extract 4 tokens.size).findIdx? (· == ")")
    | throw (.unsupported s!"unsupported sort alias: {command}")
  let endParams := endParams + 4
  let body := tokens.extract (endParams + 1) (tokens.size - 1)
  let scalar := body.size == 1 &&
    (#["Bool", "Int", "Real"].contains body[0]! || sorts.any (·.sort.toString == body[0]!) ||
      (tokens.extract 4 endParams).contains body[0]!)
  let bitvec := body.size == 5 && body.extract 0 3 == #["(", "_", "BitVec"] &&
    body[4]? == some ")" && body[3]!.toNat?.getD 0 > 0
  unless tokens[0]? == some "(" &&
      tokens[1]? == some "define-sort" && tokens[3]? == some "(" &&
      tokens.back? == some ")" && (scalar || bitvec) do
    throw (.unsupported s!"unsupported sort alias: {command}; expected Bool, Int, Real, BitVec, a declared uninterpreted sort, or a sort parameter")

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
