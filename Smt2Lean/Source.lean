namespace Smt2Lean.Source

/-- UTF-8 byte offset and one-based line/column. Columns count characters, including tabs. -/
structure Position where
  offset : Nat := 0
  line : Nat := 1
  column : Nat := 1
  deriving BEq, Inhabited, Repr

/-- The end position is exclusive. CRLF counts as one line break. -/
structure Span where
  start : Position
  stop : Position
  deriving BEq, Inhabited, Repr

/-- A command's original location, independent of native parser objects. -/
structure Ref where
  file : String
  number : Nat
  span : Span
  /-- Names introduced by :named annotations in this command. -/
  names : Array String := #[]
  deriving BEq, Inhabited, Repr

def Ref.namedContext (ref : Ref) : String :=
  if ref.names.isEmpty then "" else
    " (:named " ++ String.intercalate ", " (ref.names.toList.map reprStr) ++ ")"

def Ref.context (ref : Ref) (chc : Bool := false) : String :=
  s!"{ref.file}:{ref.span.start.line}:{ref.span.start.column}: " ++
  (if chc then "query 1: " else "") ++ s!"command {ref.number}" ++ ref.namedContext

structure Command where
  source : Ref
  text : String
  deriving BEq, Inhabited, Repr

structure Error where
  position : Position
  message : String
  deriving Repr

/-- Incremental reading keeps source commands aligned with cvc5's command stream. -/
structure Reader (input : String) where
  cursor : input.Pos := input.startPos
  position : Position := {}
  afterCR : Bool := false
  number : Nat := 1

private def Reader.advance (reader : Reader input) : Reader input := Id.run do
  let c := reader.cursor.get!
  let newline := c == '\r' || (c == '\n' && !reader.afterCR)
  return { reader with
    cursor := reader.cursor.next!
    position := {
      offset := reader.position.offset + c.utf8Size
      line := reader.position.line + if newline then 1 else 0
      column := if newline then 1 else if c == '\n' && reader.afterCR then
        reader.position.column else reader.position.column + 1 }
    afterCR := c == '\r' }

private inductive Mode where
  | normal | comment | string | quoted
  deriving BEq

/-- Read lexemes only; preserve quoted text and skip comments. No term parsing. -/
private def tokens (input : String) : Array String := Id.run do
  let mut cursor := input.startPos
  let mut result := #[]
  while cursor != input.endPos do
    let c := cursor.get!
    if c.isWhitespace then
      cursor := cursor.next!
      continue
    if c == ';' then
      while cursor != input.endPos && cursor.get! != '\n' && cursor.get! != '\r' do
        cursor := cursor.next!
      continue
    let start := cursor
    cursor := cursor.next!
    if c == '|' || c == '"' then
      while cursor != input.endPos do
        let next := cursor.get!
        cursor := cursor.next!
        if next == c then
          if c == '"' && cursor != input.endPos && cursor.get! == '"' then
            cursor := cursor.next!
          else break
    else if c != '(' && c != ')' then
      while cursor != input.endPos && !cursor.get!.isWhitespace &&
          !['(', ')', ';', '|', '"'].contains cursor.get! do
        cursor := cursor.next!
    result := result.push (String.extract start cursor)
  return result

/-- Reject unaudited attributes and recover labels before cvc5 erases or merges them. -/
def Command.withNames (command : Command) : Except String Command := do
  let parts := tokens command.text
  unless #["assert", "define-fun", "define-const"].contains (parts[1]?.getD "") do
    return command
  let mut names := #[]
  for i in [:parts.size] do
    let part := parts[i]!
    if part == ":named" then
      let some symbol := parts[i + 1]?
        | throw "expected a symbol after :named"
      -- Native parsing checks symbol syntax, freshness, and whether the body is closed.
      names := names.push (if symbol.startsWith "|" then
        ((symbol.drop 1).dropEnd 1).toString else symbol)
    else if part.startsWith ":" && !#[":pattern", ":no-pattern", ":qid"].contains part then
      throw s!"unsupported annotation: {part}"
  return { command with source := { command.source with names } }

/--
Read one complete command, preserving its bytes. This only finds boundaries;
cvc5 still parses terms and checks their syntax. SMT-LIB strings escape quotes
by doubling them; backslashes do not escape quotes or quoted-name delimiters.
-/
def Reader.next (initial : Reader input) (file : String)
    : Except Error (Option Command × Reader input) := do
  let mut reader := initial
  let mut comment := false
  while reader.cursor != input.endPos do
    let c := reader.cursor.get!
    if comment then
      comment := c != '\n' && c != '\r'
    else if c == ';' then
      comment := true
    else if !c.isWhitespace then
      break
    reader := reader.advance
  if reader.cursor == input.endPos then return (none, reader)
  unless reader.cursor.get! == '(' do
    throw { position := reader.position, message := "expected '(' at the start of a command" }
  let start := reader.position
  let begin := reader.cursor
  let mut depth := 0
  let mut mode := Mode.normal
  let mut quoteStart := start
  while reader.cursor != input.endPos do
    let c := reader.cursor.get!
    let position := reader.position
    reader := reader.advance
    match mode with
    | .comment =>
      if c == '\n' || c == '\r' then mode := .normal
    | .string =>
      if c == '"' then
        if reader.cursor != input.endPos && reader.cursor.get! == '"' then
          reader := reader.advance
        else mode := .normal
    | .quoted =>
      if c == '|' then mode := .normal
      if c == '\\' then
        throw { position, message := "backslash is not allowed in a quoted identifier" }
    | .normal =>
      if c == ';' then mode := .comment
      else if c == '"' || c == '|' then
        quoteStart := position
        mode := if c == '"' then .string else .quoted
      else if c == '(' then depth := depth + 1
      else if c == ')' then
        depth := depth - 1
        if depth == 0 then
          let source := { file, number := reader.number, span := { start, stop := reader.position } }
          return (some { source, text := String.extract begin reader.cursor },
            { reader with number := reader.number + 1 })
  let (what, opened) := match mode with
    | .string => ("string", quoteStart)
    | .quoted => ("quoted identifier", quoteStart)
    | _ => ("command", start)
  throw {
    position := reader.position
    message := s!"unexpected EOF: unterminated {what} opened at {opened.line}:{opened.column}" }

end Smt2Lean.Source
