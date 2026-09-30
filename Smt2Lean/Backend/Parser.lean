import Smt2Lean.Backend.Definitions

/-!
Parse SMT-LIB commands without solving. Track native symbol scopes and active
assertions, then inspect each check while its scope is alive.
-/

namespace Smt2Lean.Backend

/-- Only the active arrays and native assertion count roll back on pop. -/
private structure Scope where
  sorts : Nat
  declarations : Nat
  definitions : Nat
  assertions : Nat
  nativeAssertions : Nat

/-- cvc5 binds named terms directly to their bodies. Check even bodies erased by let. -/
private def validateNamedTerms (names : Array String) (tm : cvc5.TermManager) (solver : cvc5.Solver)
    (symbols : cvc5.SymbolManager) (query : ParsedQuery) (allowQuantifiers : Bool)
    : cvc5.Env Unit := do
  if names.isEmpty then return
  let parser ← cvc5.InputParser.new solver (some symbols)
  for name in names do
    parser.setStringInput s!"|{name}|"
    let body ← withoutQuantifierHints tm (← parser.nextTerm)
    validateTerm body (knownTerms query) allowQuantifiers (sorts := query.sorts)

private def invokeCommand (command : cvc5.Command) (solver : cvc5.Solver)
    (symbols : cvc5.SymbolManager) : cvc5.Env Unit := do
  let response := (← command.invoke solver symbols).trimAscii.toString
  unless response.isEmpty || response == "success" do
    throw (.error s!"{command.getCommandName}: {response}")

/-- SMT-LIB 2.6 assumptions are user-defined Boolean constants or their negations. -/
private def readAssumptions (command : Source.Command) (tm : cvc5.TermManager)
    (solver : cvc5.Solver) (symbols : cvc5.SymbolManager) (query : ParsedQuery)
    (allowQuantifiers : Bool) : cvc5.Env (Array cvc5.Term) := do
  let parts := Source.tokenize command.text
  unless parts.size ≥ 5 && parts[2]? == some "(" &&
      parts[parts.size - 2]? == some ")" && parts.back? == some ")" do
    throw (.unsupported "check-sat-assuming: expected a list of Boolean literals")
  let parser ← cvc5.InputParser.new solver (some symbols)
  let mut terms := #[]
  let mut i := 3
  while i < parts.size - 2 do
    let negative := parts[i]? == some "("
    if negative then
      unless parts[i + 1]? == some "not" && parts[i + 3]? == some ")" do
        throw (.unsupported "check-sat-assuming: expected a symbol or (not symbol)")
      i := i + 2
    let spelling := parts[i]!
    let symbol := if spelling.startsWith "|" then
      ((spelling.drop 1).dropEnd 1).toString else spelling
    let declared := (knownTerms query).any (fun declaration => declaration.term.getSymbol! == symbol) ||
      query.commands.any (·.source.names.contains symbol)
    unless declared do
      throw (.unsupported s!"check-sat-assuming: expected a user-declared or defined Boolean constant: {spelling}")
    parser.setStringInput spelling
    let term ← parser.nextTerm
    unless (← ofExcept term.getSort).isBoolean do
      throw (.unsupported s!"check-sat-assuming: expected a Boolean constant: {spelling}")
    let term ← withoutQuantifierHints tm term
    validateAssertion term (knownTerms query) allowQuantifiers query.sorts
    let term ← expandDefinitions tm query.definitions term
    validateAssertion term query.declarations allowQuantifiers query.sorts
    let term ← if negative then tm.mkTerm .NOT #[term] else pure term
    -- Negated nullary relations are Horn safety clauses. Validate the result as usual.
    let term ← if query.logic == some "HORN" && negative then
      tm.mkTerm .IMPLIES #[term[0]!, ← tm.mkFalse] else pure term
    terms := terms.push term
    i := i + if negative then 2 else 1
  unless i == parts.size - 2 do
    throw (.unsupported "check-sat-assuming: malformed literal list")
  return terms

/-- Native global equations can move: find the added term by occurrence count. -/
private def addedAssertion (before after : Array cvc5.Term) : cvc5.Env cvc5.Term := do
  let mut counts : Std.HashMap cvc5.Term Nat := {}
  for term in before do counts := counts.insert term (counts[term]?.getD 0 + 1)
  let mut added := #[]
  for term in after do
    let count := counts[term]?.getD 0
    if count == 0 then added := added.push term
    else counts := counts.insert term (count - 1)
  unless added.size == 1 && counts.toList.all (·.2 == 0) do
    throw (.error "expected exactly one new native assertion")
  return added[0]!

private def parseScript
    (input : String)
    (inspect : ParsedQuery → cvc5.Env Unit)
    (name : String) (mode : ParseMode) (singleQuery : Bool)
    (onSkipped : Source.Command → cvc5.Env Unit := fun _ => pure ()) : cvc5.Env Unit := do
  let tm      ← cvc5.TermManager.new
  let mut solver ← cvc5.Solver.new tm
  if !singleQuery then solver.setOption "incremental" "true"
  let mut symbols ← cvc5.SymbolManager.new tm
  let mut parser ← cvc5.InputParser.new solver (some symbols)
  parser.setStringInput input (name := name)
  let mut query : ParsedQuery := {}
  let mut allowQuantifiers := true
  let mut checked := false
  let mut checks := 0
  let mut scopes : Array Scope := #[]
  let mut exited := false
  let mut globalDeclarations := false
  let mut resultAvailable := false
  -- cvc5 keeps SymbolManager.isLogicSet true after reset. Track script mode here.
  let mut inStartMode := true
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
      if let some command := command? then
        let parts := Source.tokenize command.text
        if #["assert", "define-fun", "check-sat-assuming", "get-value"].contains (parts[1]?.getD "") then
          validateBitvectorIndices parts
        if parts[1]? == some "get-value" && parts.contains ":named" then
          throw (.unsupported "observational requests cannot introduce named terms")
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
      unless #["check-sat", "check-sat-assuming", "set-info", "set-option", "exit",
          "get-model", "get-proof", "get-unsat-core", "get-unsat-assumptions", "get-value",
          "get-assignment", "get-assertions", "get-info", "get-option"].contains commandName do
        resultAvailable := false
      if #["set-logic", "declare-sort", "declare-fun", "declare-const", "define-fun", "define-sort",
          "assert", "push", "pop", "reset-assertions", "check-sat", "check-sat-assuming",
          "get-assertions"].contains commandName then
        inStartMode := false
      match commandName with
      | "set-logic" =>
        let some logic := #["QF_UF", "QF_LIA", "QF_NIA", "QF_UFLIA", "QF_UFNIA",
            "UF", "LIA", "NIA", "UFLIA", "UFNIA",
            "QF_LRA", "QF_NRA", "QF_UFLRA", "QF_UFNRA", "LRA", "NRA", "UFLRA", "UFNRA",
            "QF_LIRA", "QF_NIRA", "QF_UFLIRA", "QF_UFNIRA", "LIRA", "NIRA", "UFLIRA", "UFNIRA",
            "QF_BV", "QF_UFBV", "BV", "UFBV",
            "ALL", "HORN"].find?
            (fun logic => cmd.toString == s!"(set-logic {logic})")
          | throw (.unsupported s!"unsupported logic: {cmd}")
        if logic == "HORN" && mode == .smt then
          throw (.unsupported s!"unsupported logic: {cmd}")
        invokeCommand cmd solver symbols
        allowQuantifiers := !logic.startsWith "QF_"
        query := { query with logic := some logic, invoked := query.invoked.push commandName }
      | "declare-sort" =>
        let parts := Source.tokenize command.text
        unless parts.size == 5 && parts[3]? == some "0" do
          throw (.unsupported "declare-sort: only arity 0 is supported")
        invokeCommand cmd solver symbols
        let sorts ← symbols.getDeclaredSorts
        unless sorts.size == query.sorts.size + 1 do
          throw (.error "expected one new sort declaration")
        let sort := sorts.back!
        unless sort.isUninterpretedSort do
          throw (.unsupported s!"expected an uninterpreted sort, got {sort}")
        query := { query with
          sorts := query.sorts.push { name := ← ofExcept sort.getSymbol, sort, source := some command.source }
          invoked := query.invoked.push commandName }
      | "declare-const" | "declare-fun" =>
        invokeCommand cmd solver symbols
        let terms ← symbols.getDeclaredTerms
        unless terms.size == query.declarations.size + 1 do
          throw (.error "expected one new declaration")
        let term := terms.back!
        let sort ← ofExcept term.getSort
        unless isScalarSort sort query.sorts || (← isSupportedFunction sort query.sorts) do
          throw (.unsupported s!"unsupported declaration sort: {sort}; expected Bool, Int, Real, BitVec, a declared uninterpreted sort, or a first-order function over these sorts")
        let symbol ← ofExcept term.getSymbol
        if query.declarations.any (·.name == symbol) then
          throw (.unsupported s!"duplicate declaration: {symbol}")
        query := { query with
          declarations := query.declarations.push { name := symbol, term, source := some command.source }
          invoked := query.invoked.push commandName }
      | "define-fun" =>
        validateNamedTerms command.source.names tm solver symbols query allowQuantifiers
        let before ← solver.getAssertions
        invokeCommand cmd solver symbols
        let assertions ← solver.getAssertions
        unless assertions.size == nativeCount + 1 do
          throw (.error "expected one native defining equation")
        let definition ← readDefinition (← addedAssertion before assertions) command.source query tm allowQuantifiers
        nativeCount := assertions.size
        query := { query with
          definitions := query.definitions.push definition
          invoked := query.invoked.push commandName }
      | "define-sort" =>
        validateSortAlias cmd query.sorts
        invokeCommand cmd solver symbols
        query := { query with invoked := query.invoked.push commandName }
      | "assert" =>
        let assertionNumber := query.assertions.size + 1
        try
          validateNamedTerms command.source.names tm solver symbols query allowQuantifiers
          let before ← solver.getAssertions
          invokeCommand cmd solver symbols
          let assertions ← solver.getAssertions
          unless assertions.size == nativeCount + 1 do
            throw (.error "expected one new native assertion")
          let term ← addedAssertion before assertions
          let term ← withoutQuantifierHints tm term
          validateAssertion term (knownTerms query) allowQuantifiers query.sorts
          let term ← expandDefinitions tm query.definitions term
          validateAssertion term query.declarations allowQuantifiers query.sorts
          nativeCount := assertions.size
          query := { query with assertions := query.assertions.push term }
        catch error =>
          throw (if isChc then errorWithContext s!"clause {assertionNumber}" error else error)
        query := { query with
          assertionSources := query.assertionSources.push command.source
          invoked := query.invoked.push commandName }
      | "set-info" => validateMetadata cmd
      | "set-option" =>
        if (Source.tokenize command.text)[2]? == some ":global-declarations" then
          let parts := Source.tokenize command.text
          unless parts == #["(", "set-option", ":global-declarations", "true", ")"] ||
              parts == #["(", "set-option", ":global-declarations", "false", ")"] do
            throw (.unsupported "global-declarations requires true or false")
          if !inStartMode then
            throw (.unsupported "global-declarations must be set before the logic or declarations")
          invokeCommand cmd solver symbols
          globalDeclarations := parts[3]! == "true"
          query := { query with invoked := query.invoked.push commandName }
        else validateSolverOption cmd
      | "reset" | "reset-assertions" =>
        if singleQuery then throw (.unsupported s!"unsupported command: {commandName}")
        invokeCommand cmd solver symbols
        scopes := #[]
        if commandName == "reset" then
          -- The native SymbolManager retains configuration after reset. Recreate the
          -- native session, keeping the original source reader and query numbering.
          solver ← cvc5.Solver.new tm
          solver.setOption "incremental" "true"
          symbols ← cvc5.SymbolManager.new tm
          parser ← cvc5.InputParser.new solver (some symbols)
          parser.setStringInput (String.extract reader.cursor input.endPos) (name := name)
          query := { number := checks + 1, commands := query.commands, invoked := query.invoked }
          globalDeclarations := false
          inStartMode := true
          allowQuantifiers := true
          nativeCount := 0
        else
          query := { query with assertions := #[], assertionSources := #[] }
          if !globalDeclarations then
            query := { query with sorts := #[], declarations := #[], definitions := #[] }
          nativeCount := query.definitions.size
          unless (← solver.getAssertions).size == nativeCount &&
              (← symbols.getDeclaredTerms) == query.declarations.map (·.term) &&
              (← symbols.getDeclaredSorts) == query.sorts.map (·.sort) do
            throw (.error "native and translator reset states disagree")
        query := { query with invoked := query.invoked.push commandName }
      | "get-model" | "get-proof" | "get-unsat-core" | "get-unsat-assumptions" |
          "get-value" | "get-assignment" | "get-assertions" | "get-info" | "get-option" =>
        if singleQuery then throw (.unsupported s!"unsupported command: {commandName}")
        unless resultAvailable || #["get-assertions", "get-info", "get-option"].contains commandName do
          throw (.unsupported s!"{commandName}: result request requires a preceding check in the current context")
        onSkipped command
      | "push" | "pop" =>
        let some (_, count) := scopeChange
          | throw (.unsupported s!"unsupported command: {commandName}")
        invokeCommand cmd solver symbols
        if commandName == "push" then
          let scope : Scope := {
            sorts := query.sorts.size
            declarations := query.declarations.size, definitions := query.definitions.size
            assertions := query.assertions.size, nativeAssertions := nativeCount }
          scopes := scopes ++ Array.replicate count scope
        else if count > 0 then
          let remaining := scopes.size - count
          let some scope := scopes[remaining]? | throw (.error "missing saved scope")
          query := { query with
            sorts := if globalDeclarations then query.sorts else query.sorts.extract 0 scope.sorts
            declarations := if globalDeclarations then query.declarations else query.declarations.extract 0 scope.declarations
            definitions := if globalDeclarations then query.definitions else query.definitions.extract 0 scope.definitions
            assertions := query.assertions.extract 0 scope.assertions
            assertionSources := query.assertionSources.extract 0 scope.assertions }
          nativeCount := scope.nativeAssertions + if globalDeclarations then query.definitions.size - scope.definitions else 0
          scopes := scopes.extract 0 remaining
        unless (← solver.getAssertions).size == nativeCount &&
            (← symbols.getDeclaredTerms) == query.declarations.map (·.term) &&
            (← symbols.getDeclaredSorts) == query.sorts.map (·.sort) do
          throw (.error "native and translator scopes disagree")
        query := { query with invoked := query.invoked.push commandName }
      | "check-sat" | "check-sat-assuming" =>
        let assertions ← solver.getAssertions
        unless assertions.size == nativeCount && query.assertions.size == query.assertionSources.size do
          throw (.error "assertions and source locations disagree")
        let assumptions ← if commandName == "check-sat-assuming" then
          readAssumptions command tm solver symbols query allowQuantifiers else pure #[]
        let snapshot := { query with
          source := some command.source, checkCommand := commandName
          assumptionCount := assumptions.size
          assertions := query.assertions ++ assumptions
          assertionSources := query.assertionSources ++ Array.replicate assumptions.size command.source }
        if singleQuery then query := snapshot
        checked := true
        resultAvailable := true
        checks := checks + 1
        if !singleQuery then
          inspect { snapshot with commands := query.commands.push command }
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
    (name : String := "session") (mode : ParseMode := .smt)
    (onSkipped : Source.Command → cvc5.Env Unit := fun _ => pure ()) : cvc5.Env Unit :=
  parseScript input inspect name mode false onSkipped

end Smt2Lean.Backend
