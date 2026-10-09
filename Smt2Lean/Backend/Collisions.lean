import Smt2Lean.Backend.Types

/-! Alpha-rename explicitly declared names rejected by the native parser.
The adapter only tracks binding positions; cvc5 still checks all terms and sorts. -/

namespace Smt2Lean.Backend.Collisions

inductive SExpr where
  | atom (text : String)
  | list (items : Array SExpr)
  deriving Inhabited

def sourceName (text : String) : String :=
  if text.startsWith "|" then ((text.drop 1).dropEnd 1).toString else text

def SExpr.name : SExpr → String
  | .atom text => sourceName text
  | _ => ""

partial def render : SExpr → String
  | .atom text => text
  | .list items => "(" ++ String.intercalate " " (items.toList.map render) ++ ")"

partial def read (tokens : Array String) (start : Nat) : Except String (SExpr × Nat) := do
  let some token := tokens[start]? | throw "expected an expression"
  if token == ")" then throw "unexpected ')'"
  if token != "(" then return (.atom token, start + 1)
  let mut items := #[]
  let mut next := start + 1
  while tokens[next]? != some ")" do
    let (item, stop) ← read tokens next
    items := items.push item
    next := stop
  return (.list items, next + 1)

def nameStem (tokens : Array String) : String := Id.run do
  let mut n := 0
  while tokens.any (fun token => (sourceName token).startsWith s!"smt2lean.collision.{n}.") do
    n := n + 1
  return s!"smt2lean.collision.{n}."

private abbrev Bindings := Array (String × String)
private abbrev RenameM := StateT Nat cvc5.Env

private def fresh (stem : String) : RenameM String := do
  let serial ← get
  modify (· + 1)
  return s!"{stem}{serial}"

private def localCollision (name : String) : Bool :=
  #["true", "false", "set.card"].contains name

private def constructors (query : ParsedQuery) : Array DatatypeConstructor :=
  query.datatypes.flatMap fun group => group.types.flatMap (·.constructors)

private def globals (query : ParsedQuery) : Bindings :=
  (query.definitions.map (fun d => (d.name, d.symbol.toString))).reverse ++
    (query.declarations.map (fun d => (d.name, d.term.toString))).reverse

private def constructorName (query : ParsedQuery) (name : String) : cvc5.Env (Option String) := do
  let candidates := (constructors query).filter (·.name == name)
  if candidates.size > 1 && #["true", "false"].contains name then
    throw (.unsupported s!"ambiguous constructor: {name}; use a qualified constructor")
  return candidates[0]?.map (·.parserName)

/-- Qualified constructors are closed terms: native checking resolves sort aliases. -/
private def parses (solver : cvc5.Solver) (symbols : cvc5.SymbolManager)
    (text : String) : cvc5.Env Bool := do
  try
    let parser ← cvc5.InputParser.new solver (some symbols)
    parser.setStringInput text
    return !(← parser.nextTerm).isNull
  catch _ => return false

private def qualify (query : ParsedQuery) (solver : cvc5.Solver)
    (symbols : cvc5.SymbolManager) (items : Array SExpr) : cvc5.Env SExpr := do
  let expression := SExpr.list items
  -- In particular, (as true BoolAlias) must remain the genuine Boolean constant.
  if ← parses solver symbols (render expression) then return expression
  let mut candidates := #[]
  for constructor in constructors query do
    if constructor.name != items[1]!.name || constructor.parserName == constructor.name then continue
    let candidate := SExpr.list (items.set! 1 (.atom constructor.parserName))
    if ← parses solver symbols (render candidate) then candidates := candidates.push candidate
  let #[candidate] := candidates
    | throw (.unsupported s!"unresolved or ambiguous constructor qualification: {render expression}")
  return candidate

/-- Reject duplicate binders that fresh names would otherwise hide. -/
private def binders (stem : String) (names : Array SExpr) : RenameM (Array SExpr × Bindings) := do
  let mut renamed := #[]
  let mut bindings := #[]
  for name in names do
    let .atom text := name | throw (.unsupported "expected a variable name")
    let original := sourceName text
    if localCollision original && bindings.any (·.1 == original) then
      throw (.unsupported s!"duplicate bound variable: {original}")
    let spelling ← if localCollision original then fresh stem else pure text
    renamed := renamed.push (.atom spelling)
    bindings := bindings.push (original, spelling)
  return (renamed, bindings)

private partial def term (query : ParsedQuery) (solver : cvc5.Solver)
    (symbols : cvc5.SymbolManager) (stem : String) (locals : Bindings)
    (expression : SExpr) : RenameM SExpr := do
  let lookup := fun name => (locals ++ globals query).find? (·.1 == name) |>.map (·.2)
  let .list items := expression | do
    if localCollision expression.name then
      if let some spelling := lookup expression.name then return .atom spelling
    return expression
  let head := items[0]?.map render |>.getD ""
  if head == "as" && items.size == 3 then
    if let some spelling := lookup items[1]!.name then
      return .list (items.set! 1 (.atom spelling))
    if #["true", "false"].contains items[1]!.name then return ← qualify query solver symbols items
    return expression
  if head == "_" then
    if items.size == 3 && items[1]!.name == "is" && #["true", "false"].contains items[2]!.name then
      if let some spelling ← constructorName query items[2]!.name then
        return .list (items.set! 2 (.atom spelling))
    return expression
  if (head == "forall" || head == "exists" || head == "lambda") && items.size == 3 then
    let .list variables := items[1]! | throw (.unsupported "expected bound variables")
    let pairs ← variables.mapM fun binder => do
      let .list pair := binder | throw (.unsupported "expected a sorted variable")
      unless pair.size == 2 do throw (.unsupported "expected a sorted variable")
      return pair
    let (names, added) ← binders stem (pairs.map (·[0]!))
    let variables := pairs.mapIdx fun i pair => SExpr.list (pair.set! 0 names[i]!)
    return .list #[items[0]!, .list variables, ← term query solver symbols stem (added ++ locals) items[2]!]
  if head == "let" && items.size == 3 then
    let .list entries := items[1]! | throw (.unsupported "expected let bindings")
    let pairs ← entries.mapM fun entry => do
      let .list pair := entry | throw (.unsupported "expected a let binding")
      unless pair.size == 2 do throw (.unsupported "expected a let binding")
      return pair
    let (names, added) ← binders stem (pairs.map (·[0]!))
    let entries ← pairs.mapIdxM fun i pair => do
      return SExpr.list #[names[i]!, ← term query solver symbols stem locals pair[1]!]
    return .list #[items[0]!, .list entries, ← term query solver symbols stem (added ++ locals) items[2]!]
  if head == "match" && items.size == 3 then
    let input ← term query solver symbols stem locals items[1]!
    let .list branches := items[2]! | throw (.unsupported "expected match branches")
    let branches ← branches.mapM fun branch => do
      let .list pair := branch | throw (.unsupported "expected a match branch")
      unless pair.size == 2 do throw (.unsupported "expected a pattern and branch body")
      let (pattern, added) ← match pair[0]! with
        | .atom _ => do
          if let some spelling ← constructorName query pair[0]!.name then
            pure ((if spelling == pair[0]!.name then pair[0]! else .atom spelling), #[])
          else
            let (names, added) ← binders stem #[pair[0]!]
            pure (names[0]!, added)
        | .list fields => do
          let (names, added) ← binders stem (fields.extract 1 fields.size)
          let constructor ← if let some first := fields[0]? then do
              let spelling := (← constructorName query first.name).getD first.name
              pure (if spelling == first.name then first else .atom spelling)
            else throw (.unsupported "expected a constructor pattern")
          pure (.list (#[constructor] ++ names), added)
      return SExpr.list #[pattern, ← term query solver symbols stem (added ++ locals) pair[1]!]
    return .list #[items[0]!, input, .list branches]
  if head == "!" && items.size >= 2 then
    let mut result := items.set! 1 (← term query solver symbols stem locals items[1]!)
    let mut i := 2
    while i + 1 < items.size do
      if #[":pattern", ":no-pattern"].contains (render items[i]!) then
        result := result.set! (i + 1) (← term query solver symbols stem locals items[i + 1]!)
      i := i + 2
    return .list result
  return .list (← items.mapM (term query solver symbols stem locals))

private def datatype (stem : String) (expression : SExpr) : RenameM (SExpr × Bindings) := do
  let .list constructors := expression | throw (.unsupported "expected datatype constructors")
  let mut aliases := #[]
  let mut result := #[]
  for constructor in constructors do
    let .list items := constructor | throw (.unsupported "expected a constructor declaration")
    let some original := items[0]? | throw (.unsupported "expected a constructor name")
    if #["true", "false"].contains original.name then
      if aliases.any (·.1 == original.name) then
        throw (.unsupported s!"duplicate datatype constructor: {original.name}")
      let spelling ← fresh stem
      aliases := aliases.push (original.name, spelling)
      result := result.push (.list (items.set! 0 (.atom spelling)))
    else result := result.push constructor
  return (.list result, aliases)

/-- Return adapted native input plus original/native names introduced by this command.
Active aliases come from ParsedQuery, so existing push/pop/reset handling owns their lifetime. -/
def prepare (command : Source.Command) (query : ParsedQuery) (solver : cvc5.Solver)
    (symbols : cvc5.SymbolManager) (stem : String) : cvc5.Env (Source.Command × Bindings) := do
  unless command.tokens.any (fun token => localCollision (sourceName token)) do return (command, #[])
  let kind := command.tokens[1]?.getD ""
  unless #["declare-fun", "declare-const", "define-fun", "define-fun-rec", "define-funs-rec", "define-const", "declare-datatype",
      "declare-datatypes", "assert", "check-sat-assuming", "get-value"].contains kind do
    return (command, #[])
  let (expression, stop) ← ofExcept ((read command.tokens 0).mapError cvc5.Error.error)
  unless stop == command.tokens.size do throw (.error "unexpected trailing tokens")
  let .list original := expression | throw (.error "expected a command")
  let stem := s!"{stem}{command.source.number}."
  let ((expression, aliases), _) ← (do
    let mut items := original
    let mut aliases := #[]
    if kind == "declare-datatype" && items.size == 3 then
      let (body, names) ← datatype stem items[2]!
      return (.list (items.set! 2 body), names)
    if kind == "declare-datatypes" && items.size == 3 then
      let .list groups := items[2]! | throw (.unsupported "expected datatype declaration groups")
      let mut rewritten := #[]
      for group in groups do
        let (body, names) ← datatype stem group
        aliases := aliases ++ names
        rewritten := rewritten.push body
      return (.list (items.set! 2 (.list rewritten)), aliases)
    if kind == "define-fun-rec" || kind == "define-funs-rec" then
      let (signatures, bodies) ← if kind == "define-fun-rec" && items.size == 5 then
          pure (#[SExpr.list (items.extract 1 4)], #[items[4]!])
        else if kind == "define-funs-rec" && items.size == 3 then do
          let .list signatures := items[1]! | throw (.unsupported "expected recursive signatures")
          let .list bodies := items[2]! | throw (.unsupported "expected recursive bodies")
          pure (signatures, bodies)
        else throw (.unsupported "invalid recursive definition")
      unless !signatures.isEmpty && signatures.size == bodies.size do
        throw (.unsupported "recursive group size mismatch")
      let mut renamed := #[]
      for signature in signatures do
        let .list fields := signature | throw (.unsupported "expected recursive signature")
        unless fields.size == 3 do throw (.unsupported "expected recursive signature")
        if fields[0]!.name == "set.card" then
          if (globals query ++ aliases).any (·.1 == "set.card") then
            throw (.unsupported "duplicate declaration: set.card")
          let spelling ← fresh stem
          aliases := aliases.push ("set.card", spelling)
          renamed := renamed.push (fields.set! 0 (.atom spelling))
        else renamed := renamed.push fields
      let mut signatures := #[]
      let mut rewritten := #[]
      for fields in renamed, body in bodies do
        let .list parameters := fields[1]! | throw (.unsupported "expected function parameters")
        let pairs ← parameters.mapM fun parameter => do
          let .list pair := parameter | throw (.unsupported "expected sorted parameter")
          unless pair.size == 2 do throw (.unsupported "expected sorted parameter")
          return pair
        let (names, locals) ← binders stem (pairs.map (·[0]!))
        signatures := signatures.push (.list (fields.set! 1 (.list (pairs.mapIdx fun i pair => .list (pair.set! 0 names[i]!)))))
        rewritten := rewritten.push (← term query solver symbols stem (locals ++ aliases) body)
      if kind == "define-fun-rec" then
        let .list fields := signatures[0]! | throw (.error "missing recursive signature")
        return (.list (#[items[0]!] ++ fields ++ #[rewritten[0]!]), aliases)
      return (.list #[items[0]!, .list signatures, .list rewritten], aliases)
    if #["declare-fun", "declare-const", "define-fun", "define-const"].contains kind then
      if items[1]?.map SExpr.name == some "set.card" then
        if (globals query).any (·.1 == "set.card") then
          throw (.unsupported "duplicate declaration: set.card")
        let spelling ← fresh stem
        aliases := aliases.push ("set.card", spelling)
        items := items.set! 1 (.atom spelling)
      if kind == "define-fun" && items.size == 5 then
        let .list parameters := items[2]! | throw (.unsupported "expected function parameters")
        let pairs ← parameters.mapM fun parameter => do
          let .list pair := parameter | throw (.unsupported "expected a sorted parameter")
          unless pair.size == 2 do throw (.unsupported "expected a sorted parameter")
          return pair
        let (names, locals) ← binders stem (pairs.map (·[0]!))
        items := items.set! 2 (.list (pairs.mapIdx fun i pair => .list (pair.set! 0 names[i]!)))
        items := items.set! 4 (← term query solver symbols stem locals items[4]!)
      else if kind == "define-const" && items.size == 4 then
        items := items.set! 3 (← term query solver symbols stem #[] items[3]!)
      return (.list items, aliases)
    unless items.size == 2 do throw (.unsupported s!"{kind}: expected one argument")
    return (.list (items.set! 1 (← term query solver symbols stem #[] items[1]!)), aliases)
      : RenameM (SExpr × Bindings)).run 0
  let text := render expression
  return ({ command with text, tokens := Source.tokenize text }, aliases)

def originalName (aliases : Bindings) (native : String) : String :=
  (aliases.find? (·.2 == native)).map (·.1) |>.getD native

def restoreDatatypes (aliases : Bindings) (group : DatatypeGroup) : DatatypeGroup :=
  { group with types := group.types.map fun datatype =>
      { datatype with constructors := datatype.constructors.map fun constructor =>
          { constructor with name := originalName aliases constructor.name } } }

end Smt2Lean.Backend.Collisions
