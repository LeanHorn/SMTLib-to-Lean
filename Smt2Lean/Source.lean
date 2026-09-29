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
  deriving BEq, Inhabited, Repr

def Ref.context (ref : Ref) (chc : Bool := false) : String :=
  s!"{ref.file}:{ref.span.start.line}:{ref.span.start.column}: " ++
  (if chc then "query 1: " else "") ++ s!"command {ref.number}"

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
