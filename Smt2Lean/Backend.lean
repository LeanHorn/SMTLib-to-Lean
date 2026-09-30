import cvc5
import Smt2Lean.Source
import Smt2Lean.Definitions
import Smt2Lean.Hints
import Smt.Reconstruct.Prop
import Smt.Reconstruct.Builtin
import Smt.Reconstruct.Int
import Smt.Reconstruct.UF

/-!
Parse a restricted SMT-LIB script with cvc5 without solving it.

Intercept each `check-sat` and inspect its active Bool/Int assertions without solving.
Native symbol scopes and local assertion/definition scopes follow `push` and `pop`.
Report failures with source locations, command numbers, and query/clause context.
The single-query wrapper retains its callback-after-EOF behavior.

The reconstruction imports register the handlers used by `Translate.lean`
and the reconstruction tests to turn assertion terms into Lean propositions.
-/

namespace Smt2Lean.Backend

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

/-- One validated query. Use native terms only inside `inspect`. -/
structure ParsedQuery where
  number : Nat := 1
  logic : Option String := none
  source : Option Source.Ref := none
  commands : Array Source.Command := #[]
  declarations : Array ParsedDeclaration := #[]
  definitions : Array ParsedDefinition := #[]
  assertions : Array cvc5.Term := #[]
  assertionSources : Array Source.Ref := #[]
  invoked : Array String := #[]

/-- Only the active arrays and native assertion count roll back on pop. -/
private structure Scope where
  declarations : Nat
  definitions : Nat
  assertions : Nat
  nativeAssertions : Nat

private def isScalarSort (sort : cvc5.Sort) : Bool :=
  sort.isBoolean || sort.isInteger

/-- First-order functions whose arguments and result are Bool or Int. -/
private def isSupportedFunction (sort : cvc5.Sort) : cvc5.Env Bool := do
  unless sort.isFunction do return false
  let domains ← ofExcept sort.getFunctionDomainSorts
  let result ← ofExcept sort.getFunctionCodomainSort
  return !domains.isEmpty && domains.all isScalarSort && isScalarSort result

/-- Check sorts, operators, declarations, and bound-variable scope. -/
private def validateTerm (root : cvc5.Term)
    (declarations : Array ParsedDeclaration) (allowQuantifiers : Bool)
    (bound : Array cvc5.Term := #[]) : cvc5.Env Unit := do
  for binder in bound do
    unless (← ofExcept binder.getKind) == .VARIABLE &&
        isScalarSort (← ofExcept binder.getSort) do
      throw (.unsupported "definition parameters must be Bool or Int variables")
  let mut pending : Array (cvc5.Term × Array cvc5.Term) := #[(root, bound)]
  let mut visited : Std.HashSet (cvc5.Term × Array cvc5.Term) := {}
  while !pending.isEmpty do
    let (term, bound) := pending.back!
    pending := pending.pop
    -- A shared term must be checked again when its scope changes.
    if visited.contains (term, bound) then continue
    visited := visited.insert (term, bound)
    let sort ← ofExcept term.getSort
    unless isScalarSort sort do
      throw (.unsupported s!"expected Bool or Int, got {sort}")
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
        unless isScalarSort variableSort do
          throw (.unsupported s!"unsupported bound variable sort: {variableSort}; expected Bool or Int")
        scope := scope.push binder
      pending := pending.push (children[1]!, scope)
      continue
    if kind == .APPLY_UF then
      let some function := children[0]?
        | throw (.unsupported "function application has no function")
      unless declarations.any (·.term == function) do
        throw (.unsupported s!"undeclared term: {function}")
      let signature ← ofExcept function.getSort
      unless ← isSupportedFunction signature do
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
      | .CONST_BOOLEAN | .CONST_INTEGER => pure children.isEmpty
      | .CONSTANT => do
        unless declarations.any (·.term == term) do
          throw (.unsupported s!"undeclared term: {term}")
        pure children.isEmpty
      | .VARIABLE => do
        unless bound.contains term do
          throw (.unsupported s!"unbound variable: {term}")
        pure children.isEmpty
      | .NOT | .NEG | .ABS => pure (children.size == 1)
      | .ITE => pure (children.size == 3)
      | .AND | .OR | .XOR | .IMPLIES | .DISTINCT | .ADD | .SUB | .MULT =>
        pure (children.size >= 2)
      -- cvc5 expands chains into conjunctions of adjacent binary comparisons.
      | .EQUAL | .LT | .LEQ | .GT | .GEQ => pure (children.size == 2)
      | _ => throw (.unsupported s!"unsupported operator: {kind}")
    unless validArity do
      throw (.unsupported s!"unsupported arity for {kind}: {children.size}")
    pending := pending ++ children.map (·, bound)

/-- Assertions must be Boolean and contain only the supported, scoped terms. -/
def validateAssertion (root : cvc5.Term)
    (declarations : Array ParsedDeclaration) (allowQuantifiers : Bool := true) : cvc5.Env Unit := do
  unless (← ofExcept root.getSort).isBoolean do
    throw (.unsupported "expected a Bool assertion")
  validateTerm root declarations allowQuantifiers

private def knownTerms (query : ParsedQuery) : Array ParsedDeclaration :=
  query.declarations ++ query.definitions.map fun d =>
    { name := d.symbol.toString, term := d.symbol, source := some d.source }

/-- cvc5 binds named terms directly to their bodies. Check even bodies erased by let. -/
private def validateNamedTerms (names : Array String) (tm : cvc5.TermManager) (solver : cvc5.Solver)
    (symbols : cvc5.SymbolManager) (query : ParsedQuery) (allowQuantifiers : Bool)
    : cvc5.Env Unit := do
  if names.isEmpty then return
  let parser ← cvc5.InputParser.new solver (some symbols)
  for name in names do
    parser.setStringInput s!"|{name}|"
    let body ← withoutQuantifierHints tm (← parser.nextTerm)
    validateTerm body (knownTerms query) allowQuantifiers

/-- cvc5 stores each define-fun as `symbol = body`, using a lambda for parameters. -/
private def readDefinition (equation : cvc5.Term) (source : Source.Ref)
    (query : ParsedQuery) (tm : cvc5.TermManager) (allowQuantifiers : Bool)
    : cvc5.Env ParsedDefinition := do
  unless (← ofExcept equation.getKind) == .EQUAL && equation.getNumChildren == 2 do
    throw (.error "expected a native defining equation")
  let symbol := equation[0]!
  let sort ← ofExcept symbol.getSort
  unless (← ofExcept symbol.getKind) == .CONSTANT &&
      (isScalarSort sort || (← isSupportedFunction sort)) do
    throw (.unsupported s!"unsupported definition signature: {sort}; expected Bool/Int")
  let value := equation[1]!
  let (parameters, body) ← if (← ofExcept value.getKind) == .LAMBDA then do
      unless value.getNumChildren == 2 && (← ofExcept value[0]!.getKind) == .VARIABLE_LIST do
        throw (.error "expected a native definition lambda")
      pure (value[0]!.getChildren, value[1]!)
    else pure (#[], value)
  let body ← withoutQuantifierHints tm body
  -- Check before expansion as well: even discarded arguments must be supported.
  validateTerm body (knownTerms query) allowQuantifiers parameters
  let body ← expandDefinitions tm query.definitions body
  validateTerm body query.declarations allowQuantifiers parameters
  return { symbol, parameters, body, source }

/-- These metadata fields never become assumptions or select a proof target. -/
private def validateMetadata (command : cvc5.Command) : cvc5.Env Unit := do
  -- The binding exposes no command arguments; inspect cvc5's canonical printing.
  let text := command.toString
  let keys := #[":status", ":source", ":category", ":license", ":notes"]
  if keys.any (fun key => text.startsWith s!"(set-info {key} ") then return
  if text == "(set-info :smt-lib-version 2.6)" then return
  throw (.unsupported s!"unsupported metadata: {text}")

/-- Validate solver controls without applying them. Native parsing alone does not check values. -/
private def validateSolverOption (command : cvc5.Command) : cvc5.Env Unit := do
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

private def invokeCommand (command : cvc5.Command) (solver : cvc5.Solver)
    (symbols : cvc5.SymbolManager) : cvc5.Env Unit := do
  let response := (← command.invoke solver symbols).trimAscii.toString
  unless response.isEmpty || response == "success" do
    throw (.error s!"{command.getCommandName}: {response}")

/-- Add a location without changing the native error category. -/
def errorWithContext (context : String) : cvc5.Error → cvc5.Error
  | .error message => .error s!"{context}: {message}"
  | .recoverable message => .recoverable s!"{context}: {message}"
  | .unsupported message => .unsupported s!"{context}: {message}"
  | .option message => .option s!"{context}: {message}"
  | .missingValue => .error s!"{context}: missing native value"

private def parseScript
    (input : String)
    (inspect : ParsedQuery → cvc5.Env Unit)
    (name : String) (mode : ParseMode) (singleQuery : Bool) : cvc5.Env Unit := do
  let tm      ← cvc5.TermManager.new
  let solver  ← cvc5.Solver.new tm
  if !singleQuery then solver.setOption "incremental" "true"
  let symbols ← cvc5.SymbolManager.new tm
  let parser  ← cvc5.InputParser.new solver (some symbols)
  parser.setStringInput input (name := name)
  let mut query : ParsedQuery := {}
  let mut allowQuantifiers := true
  let mut checked := false
  let mut checks := 0
  let mut scopes : Array Scope := #[]
  let mut exited := false
  let mut reader : Source.Reader input := {}
  -- cvc5 counts defining equations too; query.assertions keeps only source assertions.
  let mut nativeCount := 0
  while true do
    let isChc := mode == .chc || query.logic == some "HORN"
    let (command?, rest) ← match reader.next name with
      | .ok result => pure result
      | .error error =>
        let source : Source.Ref := {
          file := name, number := reader.number
          span := { start := error.position, stop := error.position } }
        throw (errorWithContext (source.context isChc query.number) (.error error.message))
    reader := rest
    let eof : Source.Ref := {
      file := name, number := reader.number
      span := { start := reader.position, stop := reader.position } }
    let context := (command?.map (·.source) |>.getD eof).context isChc query.number
    let command? ← command?.mapM fun command => do
      match command.withNames with
      | .ok command => pure command
      | .error message => throw (errorWithContext context (.unsupported message))
    let context := (command?.map (·.source) |>.getD eof).context isChc query.number
    try
      if !singleQuery && exited && command?.isSome then
        throw (.unsupported "unexpected command after exit")
      let scopeChange ← if singleQuery then pure none else do
        match command? with
        | none => pure none
        | some command => match command.scopeChange with
          | .ok change => pure change
          | .error message => throw (.unsupported message)
      if let some ("pop", count) := scopeChange then
        if count > scopes.size then
          throw (.error s!"pop {count} exceeds active scope depth {scopes.size}")
      let cmd ← parser.nextCommand
      if cmd.isNull then
        unless command?.isNone do throw (.error "source reader and cvc5 command streams disagree")
        break
      let some command := command?
        | throw (.error "source reader and cvc5 command streams disagree")
      let commandName := cmd.getCommandName
      if exited then
        throw (.unsupported s!"unexpected command after exit: {commandName}")
      if singleQuery && checked && commandName != "set-info" && commandName != "exit" then
        throw (.unsupported s!"unexpected command after check-sat: {commandName}")
      match commandName with
      | "set-logic" =>
        let some logic := #["QF_UF", "QF_LIA", "QF_NIA", "QF_UFLIA", "QF_UFNIA",
            "UF", "LIA", "NIA", "UFLIA", "UFNIA", "ALL", "HORN"].find?
            (fun logic => cmd.toString == s!"(set-logic {logic})")
          | throw (.unsupported s!"unsupported logic: {cmd}")
        if logic == "HORN" && mode == .smt then
          throw (.unsupported s!"unsupported logic: {cmd}")
        invokeCommand cmd solver symbols
        allowQuantifiers := !logic.startsWith "QF_"
        query := { query with logic := some logic, invoked := query.invoked.push commandName }
      | "declare-const" | "declare-fun" =>
        invokeCommand cmd solver symbols
        let terms ← symbols.getDeclaredTerms
        unless terms.size == query.declarations.size + 1 do
          throw (.error "expected one new declaration")
        let term := terms.back!
        let sort ← ofExcept term.getSort
        unless isScalarSort sort || (← isSupportedFunction sort) do
          throw (.unsupported s!"unsupported declaration sort: {sort}; expected Bool, Int, or a function with Bool/Int arguments and result")
        let symbol ← ofExcept term.getSymbol
        if query.declarations.any (·.name == symbol) then
          throw (.unsupported s!"duplicate declaration: {symbol}")
        query := { query with
          declarations := query.declarations.push { name := symbol, term, source := some command.source }
          invoked := query.invoked.push commandName }
      | "define-fun" =>
        validateNamedTerms command.source.names tm solver symbols query allowQuantifiers
        invokeCommand cmd solver symbols
        let assertions ← solver.getAssertions
        unless assertions.size == nativeCount + 1 do
          throw (.error "expected one native defining equation")
        let definition ← readDefinition assertions.back! command.source query tm allowQuantifiers
        nativeCount := assertions.size
        query := { query with
          definitions := query.definitions.push definition
          invoked := query.invoked.push commandName }
      | "define-sort" =>
        validateSortAlias cmd
        invokeCommand cmd solver symbols
        query := { query with invoked := query.invoked.push commandName }
      | "assert" =>
        let assertionNumber := query.assertions.size + 1
        try
          validateNamedTerms command.source.names tm solver symbols query allowQuantifiers
          invokeCommand cmd solver symbols
          let assertions ← solver.getAssertions
          unless assertions.size == nativeCount + 1 do
            throw (.error "expected one new native assertion")
          let some term := assertions.back?
            | throw (.error "assert command did not store a formula")
          let term ← withoutQuantifierHints tm term
          validateAssertion term (knownTerms query) allowQuantifiers
          let term ← expandDefinitions tm query.definitions term
          validateAssertion term query.declarations allowQuantifiers
          nativeCount := assertions.size
          query := { query with assertions := query.assertions.push term }
        catch error =>
          throw (if isChc then errorWithContext s!"clause {assertionNumber}" error else error)
        query := { query with
          assertionSources := query.assertionSources.push command.source
          invoked := query.invoked.push commandName }
      | "set-info" => validateMetadata cmd
      | "set-option" => validateSolverOption cmd
      | "push" | "pop" =>
        let some (_, count) := scopeChange
          | throw (.unsupported s!"unsupported command: {commandName}")
        invokeCommand cmd solver symbols
        if commandName == "push" then
          let scope : Scope := {
            declarations := query.declarations.size, definitions := query.definitions.size
            assertions := query.assertions.size, nativeAssertions := nativeCount }
          scopes := scopes ++ Array.replicate count scope
        else if count > 0 then
          let remaining := scopes.size - count
          let some scope := scopes[remaining]? | throw (.error "missing saved scope")
          query := { query with
            declarations := query.declarations.extract 0 scope.declarations
            definitions := query.definitions.extract 0 scope.definitions
            assertions := query.assertions.extract 0 scope.assertions
            assertionSources := query.assertionSources.extract 0 scope.assertions }
          nativeCount := scope.nativeAssertions
          scopes := scopes.extract 0 remaining
        unless (← solver.getAssertions).size == nativeCount &&
            (← symbols.getDeclaredTerms) == query.declarations.map (·.term) do
          throw (.error "native and translator scopes disagree")
        query := { query with invoked := query.invoked.push commandName }
      | "check-sat" =>
        let assertions ← solver.getAssertions
        unless assertions.size == nativeCount && query.assertions.size == query.assertionSources.size do
          throw (.error "assertions and source locations disagree")
        query := { query with source := some command.source }
        checked := true
        checks := checks + 1
        if !singleQuery then
          inspect { query with commands := query.commands.push command }
          query := { query with number := checks + 1 }
      | "exit" =>
        unless checked do throw (.error "exit before check-sat")
        exited := true
      | _ => throw (.unsupported s!"unsupported command: {commandName}")
      query := { query with commands := query.commands.push command }
    catch error => throw (errorWithContext context error)
  unless checked do
    let source : Source.Ref := {
      file := name, number := reader.number
      span := { start := reader.position, stop := reader.position } }
    throw (errorWithContext (source.context (mode == .chc || query.logic == some "HORN") query.number)
      (.error (if singleQuery then "expected one check-sat" else "expected at least one check-sat")))
  if singleQuery then inspect query

/-- Parse one query and call `inspect` after the whole input validates.
Only metadata and a final exit may follow its check; scope commands are rejected. -/
def parseAndInspectQuery (input : String) (inspect : ParsedQuery → cvc5.Env Unit)
    (name : String := "backend-smoke") (mode : ParseMode := .smt) : cvc5.Env Unit :=
  parseScript input inspect name mode true

/-- Inspect each check while its native scope is active. Never execute a solver query.
Callbacks see active terms and the command history through that check. Reconstruct
inside the callback; publish results only after this function succeeds, since a
later command can still fail. At least one check is required. -/
def parseAndInspectSession (input : String) (inspect : ParsedQuery → cvc5.Env Unit)
    (name : String := "session") (mode : ParseMode := .smt) : cvc5.Env Unit :=
  parseScript input inspect name mode false

end Smt2Lean.Backend
