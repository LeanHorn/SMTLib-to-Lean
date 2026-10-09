import Smt2Lean.Backend.Sorts
import Smt2Lean.Backend.Definitions
import Smt2Lean.Backend.Session
import Smt2Lean.Backend.Datatypes
import Smt2Lean.Backend.MatchWildcards
import Smt2Lean.Backend.Collisions

/-!
Parse SMT-LIB commands without solving. Track native symbol scopes and active
assertions, then inspect each check while its scope is alive.
-/

namespace Smt2Lean.Backend

/-- cvc5 binds named terms directly to their bodies. Check even bodies erased by let. -/
private def validateNamedTerms (names : Array String) (tm : cvc5.TermManager) (solver : cvc5.Solver)
    (symbols : cvc5.SymbolManager) (query : ParsedQuery) (allowQuantifiers : Bool)
    : cvc5.Env Unit := do
  if names.isEmpty then return
  let parser ← cvc5.InputParser.new solver (some symbols)
  for name in names do
    parser.setStringInput s!"|{name}|"
    let body ← withoutQuantifierHints tm (← parser.nextTerm)
    validateTerm body (knownTerms query) allowQuantifiers (sorts := query.valueSorts) (constructors := query.arrayConstructors)

private def invokeCommand (command : cvc5.Command) (solver : cvc5.Solver)
    (symbols : cvc5.SymbolManager) : cvc5.Env Unit := do
  let response := (← command.invoke solver symbols).trimAscii.toString
  unless response.isEmpty || response == "success" do
    throw (.error s!"{command.getCommandName}: {response}")

/-- Parse supported Boolean assumptions without asserting them in the native solver.
They belong only to the current check's snapshot, as specified by SMT-LIB 2.7. -/
private def readAssumptions (command : Source.Command) (tm : cvc5.TermManager)
    (solver : cvc5.Solver) (symbols : cvc5.SymbolManager) (query : ParsedQuery)
    (allowQuantifiers : Bool) : cvc5.Env (Array (cvc5.Term × cvc5.Term)) := do
  let parts := command.tokens
  unless parts.size ≥ 5 && parts[2]? == some "(" &&
      parts[parts.size - 2]? == some ")" && parts.back? == some ")" do
    throw (.unsupported "check-sat-assuming: expected a list of Boolean terms")
  let parser ← cvc5.InputParser.new solver (some symbols)
  parser.setStringInput (String.intercalate " " (parts.extract 3 (parts.size - 2)).toList)
  let mut terms := #[]
  let mut query := query
  while true do
    let term ← parser.nextTerm
    if term.isNull then break
    unless (← ofExcept term.getSort).isBoolean do
      throw (.unsupported "check-sat-assuming: expected a Boolean term")
    query ← query.collectTermSorts #[term] command.source
    let term ← withoutQuantifierHints tm term
    validateAssertion term (knownTerms query) allowQuantifiers query.valueSorts query.arrayConstructors
    let surface := term
    let term ← SourceLets.erase tm query.sourceLets term
    let term ← expandDefinitions tm query.definitions term
    validateAssertion term query.declarations allowQuantifiers query.valueSorts query.arrayConstructors
    -- Preserve the established Horn safety-clause representation for negated assumptions.
    let term ← if query.logic == some "HORN" && (← ofExcept term.getKind) == .NOT then
      tm.mkTerm .IMPLIES #[term[0]!, ← tm.mkFalse] else pure term
    let surface ← if query.logic == some "HORN" && surface.getKind! == .NOT then
      tm.mkTerm .IMPLIES #[surface[0]!, ← tm.mkFalse] else pure surface
    terms := terms.push (term, surface)
  return terms

/-- Native global equations can move: find the added term by occurrence count. -/
private def addedAssertions (before after : Array cvc5.Term) : cvc5.Env (Array cvc5.Term) := do
  let mut counts : Std.HashMap cvc5.Term Nat := {}
  for term in before do counts := counts.insert term (counts[term]?.getD 0 + 1)
  let mut added := #[]
  for term in after do
    let count := counts[term]?.getD 0
    if count == 0 then added := added.push term
    else counts := counts.insert term (count - 1)
  unless counts.toList.all (·.2 == 0) do
    throw (.error "native command removed an existing assertion")
  return added

private def addedAssertion (before after : Array cvc5.Term) : cvc5.Env cvc5.Term := do
  let #[term] ← addedAssertions before after
    | throw (.error "expected exactly one new native assertion")
  return term

private def parseScript
    (input : String)
    (inspect : ParsedQuery → cvc5.Env Unit)
    (name : String) (mode : ParseMode) (singleQuery : Bool)
    (onSkipped : Source.Command → cvc5.Env Unit := fun _ => pure ())
    (sources : Array Source.Ref := #[]) : cvc5.Env Unit := do
  let tm      ← cvc5.TermManager.new
  let mut solver ← cvc5.Solver.new tm
  if !singleQuery then solver.setOption "incremental" "true"
  let mut symbols ← cvc5.SymbolManager.new tm
  let mut parser ← cvc5.InputParser.new solver (some symbols)
  let inputTokens := Source.tokenize input
  let initialArrays := ConstantArrays.initial inputTokens
  let wildcardStem := MatchWildcards.nameStem inputTokens
  let letStem := SourceLets.nameStem inputTokens
  let collisionStem := Collisions.nameStem inputTokens
  let mut session : Session := { arrays := initialArrays, query := { manager := some tm } }
  let adaptArrays := inputTokens.any (fun token => token == "const" || token == "|const|")
  let mut allowQuantifiers := true
  let mut checked := false
  let mut checks := 0
  let mut exited := false
  let mut resultAvailable := false
  -- cvc5 keeps SymbolManager.isLogicSet true after reset. Track script mode here.
  let mut inStartMode := true
  let mut reader : Source.Reader input := {}
  while true do
    let isChc := mode == .chc || session.query.logic == some "HORN"
    let (command?, rest) ← match reader.next name with
      | .ok result => pure result
      | .error error =>
        let source : Source.Ref := {
          file := name, number := reader.number
          span := { start := error.position, stop := error.position } }
        throw (errorWithContext (source.context isChc session.query.number) (.error error.message))
    reader := rest
    let command? := command?.map fun command =>
      { command with source := sources[command.source.number - 1]?.getD command.source }
    let eof : Source.Ref := {
      file := name, number := reader.number
      span := { start := reader.position, stop := reader.position } }
    let context := (command?.map (·.source) |>.getD eof).context isChc session.query.number
    let command? ← command?.mapM fun command => do
      match command.withNames with
      | .ok command => pure command
      | .error message => throw (errorWithContext context (.unsupported message))
    let context := (command?.map (·.source) |>.getD eof).context isChc session.query.number
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
        if count > session.depth then
          throw (.error s!"pop {count} exceeds active scope depth {session.depth}")
      if let some command := command? then
        let parts := command.tokens
        if #["assert", "define-fun", "define-fun-rec", "define-funs-rec", "define-const", "check-sat-assuming", "get-value"].contains (parts[1]?.getD "") then
          validateBitvectorIndices parts
        if #["get-value", "check-sat-assuming"].contains (parts[1]?.getD "") && parts.contains ":named" then
          throw (.unsupported "observational requests and assumptions cannot introduce named terms")
      let mut arrayConstants := #[]
      let mut namedConstants := #[]
      let mut renamedBindings := #[]
      let text ← match command? with
        | none => pure ""
        | some command => do
          let command ← ofExcept (MatchWildcards.prepare command wildcardStem |>.mapError cvc5.Error.error)
          let (command, lets) ← SourceLets.prepare command solver symbols letStem
          session := session.mapQuery fun query => { query with sourceLets := query.sourceLets ++ lets }
          let (command, aliases) ← Collisions.prepare command session.query solver symbols collisionStem
          renamedBindings := aliases
          let kind := command.tokens[1]?.getD ""
          if adaptArrays && #["declare-sort", "declare-fun", "declare-const", "define-sort",
              "define-fun", "define-fun-rec", "define-funs-rec", "define-const", "declare-datatype", "declare-datatypes", "assert", "push", "check-sat", "check-sat-assuming", "get-value"].contains kind then
            let (_, state) ← (ConstantArrays.initializeAliases tm solver symbols).run session.arrays
            session := { session with arrays := state }
          if adaptArrays then
            let ((text, constants, names), state) ← (ConstantArrays.prepare command solver symbols session.query).run session.arrays
            session := { session with arrays := state }
            arrayConstants := constants
            namedConstants := names
            session := session.mapQuery fun query => { query with arrayConstructors := state.constructors }
            pure text
          else pure command.text
      parser.setStringInput text (name := name)
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
      if #["set-logic", "declare-sort", "declare-fun", "declare-const", "define-fun", "define-fun-rec", "define-sort",
          "declare-datatype", "declare-datatypes", "assert", "push", "pop", "reset-assertions", "check-sat", "check-sat-assuming",
          "get-assertions"].contains commandName then
        inStartMode := false
      match commandName with
      | "set-logic" =>
        let some logic := #["QF_UF", "QF_LIA", "QF_NIA", "QF_UFLIA", "QF_UFNIA",
            "UF", "LIA", "NIA", "UFLIA", "UFNIA",
            "QF_LRA", "QF_NRA", "QF_UFLRA", "QF_UFNRA", "LRA", "NRA", "UFLRA", "UFNRA",
            "QF_LIRA", "QF_NIRA", "QF_UFLIRA", "QF_UFNIRA", "LIRA", "NIRA", "UFLIRA", "UFNIRA",
            "QF_BV", "QF_UFBV", "BV", "UFBV",
            "QF_DT", "QF_UFDT", "QF_UFDTLIA", "DT", "UFDT", "UFDTLIA",
            "QF_AX", "QF_ABV", "QF_AUFBV", "QF_ALIA", "QF_AUFLIA", "QF_AUFNIA",
            "ALIA", "AUFLIA", "AUFLIRA", "AUFNIA", "AUFNIRA", "ABV", "AUFBV",
            "ALL", "HORN"].find?
            (fun logic => cmd.toString == s!"(set-logic {logic})")
          | throw (.unsupported s!"unsupported logic: {cmd}")
        if logic == "HORN" && mode == .smt then
          throw (.unsupported s!"unsupported logic: {cmd}")
        invokeCommand cmd solver symbols
        if adaptArrays then
          let (_, state) ← (ConstantArrays.initializeAliases tm solver symbols).run session.arrays
          session := { session with arrays := state }
        allowQuantifiers := !logic.startsWith "QF_"
        session := session.mapQuery fun query => { query with logic := some logic, invoked := query.invoked.push commandName }
      | "declare-sort" =>
        let parts := command.tokens
        let some arity := (parts[3]?.getD "").toNat?
          | throw (.unsupported "declare-sort: expected a nonnegative arity")
        unless parts.size == 5 && arity ≤ 4294967295 do
          throw (.unsupported "declare-sort: arity exceeds native limit")
        invokeCommand cmd solver symbols
        if arity > 0 then
          let nativeName := (Source.tokenize cmd.toString)[2]!
          -- A used constructor needs at least this many argument tokens.
          if adaptArrays && arity ≤ inputTokens.size then
            let (_, state) ← (ConstantArrays.rememberSortConstructor solver symbols
              parts[2]! arity).run session.arrays
            session := { session with arrays := state }
          session := session.mapQuery fun query => { query with
            sortConstructors := query.sortConstructors.push (nativeName, arity)
            commands := query.commands.push command
            invoked := query.invoked.push commandName }
          continue
        let sorts ← symbols.getDeclaredSorts
        unless sorts.size == session.query.sorts.size + 1 do
          throw (.error "expected one new sort declaration")
        let sort := sorts.back!
        unless sort.isUninterpretedSort do
          throw (.unsupported s!"expected an uninterpreted sort, got {sort}")
        if adaptArrays then
          let (_, state) ← (ConstantArrays.rememberSort solver symbols sort parts[2]!).run session.arrays
          session := { session with arrays := state }
        let symbol ← ofExcept sort.getSymbol
        session := session.mapQuery fun query => { query with
          sorts := query.sorts.push { name := symbol, sort, source := some command.source }
          invoked := query.invoked.push commandName }
      | "declare-datatype" | "declare-datatypes" =>
        invokeCommand cmd solver symbols
        let fresh ← datatypeSorts cmd solver symbols
        session := { session with query := ← session.query.collectSorts fresh command.source }
        let group ← readDatatypes fresh session.query command.source
        let group := Collisions.restoreDatatypes renamedBindings group
        if adaptArrays then
          for datatype in group.types do
            let (_, state) ← (ConstantArrays.rememberSort solver symbols datatype.sort
              datatype.sort.toString).run session.arrays
            session := { session with arrays := state }
        session := session.mapQuery fun query => { query with
          datatypes := query.datatypes.push group
          invoked := query.invoked.push commandName }
      | "declare-const" | "declare-fun" =>
        invokeCommand cmd solver symbols
        let terms := SourceLets.sourceDeclarations session.query.sourceLets (ConstantArrays.sourceDeclarations session.arrays (← symbols.getDeclaredTerms))
        unless terms.size == session.query.nativeDeclarations.size + 1 do
          throw (.error "expected one new declaration")
        let term := terms.back!
        let sort ← ofExcept term.getSort
        session := { session with query := ← session.query.collectSorts #[sort] command.source }
        unless isValueSort sort session.query.valueSorts || (← isSupportedFunction sort session.query.valueSorts) do
          throw (.unsupported s!"unsupported declaration sort: {sort}; expected a supported value sort or first-order function")
        let symbol := Collisions.originalName renamedBindings (← ofExcept term.getSymbol)
        if session.query.declarations.any (·.name == symbol) then
          throw (.unsupported s!"duplicate declaration: {symbol}")
        session := session.mapQuery fun query => { query with
          declarations := query.declarations.push { name := symbol, term, source := some command.source }
          invoked := query.invoked.push commandName }
      | "define-fun" =>
        validateNamedTerms command.source.names tm solver symbols session.query allowQuantifiers
        let before ← solver.getAssertions
        invokeCommand cmd solver symbols
        let assertions ← solver.getAssertions
        unless assertions.size == session.nativeCount + 1 do
          throw (.error "expected one native defining equation")
        let equation ← addedAssertion before assertions
        session := { session with query := ← session.query.collectTermSorts #[equation] command.source }
        let definition ← readDefinition equation command.source session.query tm allowQuantifiers
        let definition := { definition with
          arrayConstants := arrayConstants
          name := Collisions.originalName renamedBindings definition.name }
        session := { session with nativeCount := assertions.size }
        session := session.mapQuery fun query => { query with
          definitions := query.definitions.push definition
          invoked := query.invoked.push commandName }
      | "define-fun-rec" =>
        validateNamedTerms command.source.names tm solver symbols session.query allowQuantifiers
        let before ← solver.getAssertions
        invokeCommand cmd solver symbols
        let assertions ← solver.getAssertions
        let equations ← addedAssertions before assertions
        let query ← session.query.collectTermSorts equations command.source
        let query ← readRecursiveDefinitions equations command.source query tm allowQuantifiers arrayConstants
        let query := { query with declarations := query.declarations.map fun (d : ParsedDeclaration) =>
          { d with name := Collisions.originalName renamedBindings d.name } }
        session := { session with
          nativeCount := assertions.size
          query := { query with invoked := query.invoked.push commandName } }
      | "define-sort" =>
        validateSortAlias cmd session.query.valueSorts session.query.sortConstructors
        invokeCommand cmd solver symbols
        session := session.mapQuery fun query => { query with invoked := query.invoked.push commandName }
      | "assert" =>
        let assertionNumber := session.query.assertions.size + 1
        try
          validateNamedTerms command.source.names tm solver symbols session.query allowQuantifiers
          let before ← solver.getAssertions
          invokeCommand cmd solver symbols
          let assertions ← solver.getAssertions
          unless assertions.size == session.nativeCount + 1 do
            throw (.error "expected one new native assertion")
          let term ← addedAssertion before assertions
          session := { session with query := ← session.query.collectTermSorts #[term] command.source }
          let term ← withoutQuantifierHints tm term
          validateAssertion term (knownTerms session.query) allowQuantifiers session.query.valueSorts session.query.arrayConstructors
          let surface := term
          let term ← SourceLets.erase tm session.query.sourceLets term
          let term ← expandDefinitions tm session.query.definitions term
          validateAssertion term session.query.declarations allowQuantifiers session.query.valueSorts session.query.arrayConstructors
          session := { session with nativeCount := assertions.size }
          session := session.mapQuery fun query => { query with
            assertions := query.assertions.push { term, surface := some surface, source := command.source, arrayConstants } }
        catch error =>
          throw (if isChc then errorWithContext s!"clause {assertionNumber}" error else error)
        session := session.mapQuery fun query => { query with
          invoked := query.invoked.push commandName }
      | "set-info" => validateMetadata cmd
      | "set-option" =>
        if command.tokens[2]? == some ":global-declarations" then
          let parts := command.tokens
          unless parts == #["(", "set-option", ":global-declarations", "true", ")"] ||
              parts == #["(", "set-option", ":global-declarations", "false", ")"] do
            throw (.unsupported "global-declarations requires true or false")
          if !inStartMode then
            throw (.unsupported "global-declarations must be set before the logic or declarations")
          invokeCommand cmd solver symbols
          session := { session with globalDeclarations := parts[3]! == "true" }
          session := session.mapQuery fun query => { query with invoked := query.invoked.push commandName }
        else validateSolverOption cmd
      | "reset" | "reset-assertions" =>
        if singleQuery then throw (.unsupported s!"unsupported command: {commandName}")
        invokeCommand cmd solver symbols
        if commandName == "reset" then
          -- cvc5 retains SymbolManager configuration after reset; recreate the session.
          solver ← cvc5.Solver.new tm
          solver.setOption "incremental" "true"
          symbols ← cvc5.SymbolManager.new tm
          parser ← cvc5.InputParser.new solver (some symbols)
          session := session.reset initialArrays (checks + 1)
          inStartMode := true
          allowQuantifiers := true
        else
          session := session.clearAssertions
          session.checkNative solver symbols "reset states"
        session := session.mapQuery fun query => { query with invoked := query.invoked.push commandName }
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
          session := session.push count
        else
          session ← session.pop count
        session.checkNative solver symbols "scopes"
        session := session.mapQuery fun query => { query with invoked := query.invoked.push commandName }
      | "check-sat" | "check-sat-assuming" =>
        let assertions ← solver.getAssertions
        unless assertions.size == session.nativeCount do
          throw (.error "native and translator assertion counts disagree")
        let assumptions ← if commandName == "check-sat-assuming" then
          readAssumptions { command with text, tokens := Source.tokenize text }
            tm solver symbols session.query allowQuantifiers else pure #[]
        let query ← session.query.collectTermSorts (assumptions.flatMap fun (a, b) => #[a, b]) command.source
        let snapshot := { query with
          source := some command.source, checkCommand := commandName
          assumptionCount := assumptions.size
          assertions := session.query.recursiveDefinitions.map (·.equation) ++ session.query.assertions ++ assumptions.map (fun (term, surface) => { term, surface := some surface, source := command.source, arrayConstants }) }
        if singleQuery then session := { session with query := snapshot }
        checked := true
        resultAvailable := true
        checks := checks + 1
        if !singleQuery then
          inspect { snapshot with commands := session.query.commands.push command }
          session := session.mapQuery fun query => { query with number := checks + 1 }
      | "exit" =>
        unless checked do throw (.error "exit before check-sat")
        exited := true
      | _ => throw (.unsupported s!"unsupported command: {commandName}")
      session := session.mapQuery fun query => { query with
        commands := query.commands.push command
        namedArrayConstants := query.namedArrayConstants ++ namedConstants }
    catch error => throw (errorWithContext context error)
  unless checked do
    let source : Source.Ref := {
      file := name, number := reader.number
      span := { start := reader.position, stop := reader.position } }
    throw (errorWithContext (source.context (mode == .chc || session.query.logic == some "HORN") session.query.number)
      (.error (if singleQuery then "expected one check-sat" else "expected at least one check-sat")))
  if singleQuery then inspect session.query

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
    (onSkipped : Source.Command → cvc5.Env Unit := fun _ => pure ())
    (sources : Array Source.Ref := #[]) : cvc5.Env Unit :=
  parseScript input inspect name mode false onSkipped sources

end Smt2Lean.Backend
