import Smt2Lean.Source

open Smt2Lean.Source

private def require (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def readAll (input : String) : IO (Array Command × Position) := do
  let mut reader : Reader input := {}
  let mut commands := #[]
  while true do
    let (command?, rest) ← match reader.next "source.smt2" with
      | .ok result => pure result
      | .error error => throw (IO.userError s!"{repr error}")
    reader := rest
    let some command := command? | break
    commands := commands.push command
  return (commands, reader.position)

def main : IO Unit := do
  let leading := "; α )\r\n"
  let metadata := "(set-info :source \"(; \"\"quoted\"\" \\u{3bb})\")"
  let declaration := "(declare-const |p (;) \"q\"| Bool)"
  let assertion := "(assert\n  (and |p (;) \"q\"| ; ignored )\n       true))"
  let check := "(check-sat)"
  let input := leading ++ metadata ++ "\r\n  " ++ declaration ++ "\r\n" ++
    assertion ++ " " ++ check ++ "; final comment )"
  let (commands, eof) ← readAll input
  require (commands.map (·.text) == #[metadata, declaration, assertion, check])
    "commands were split inside comments, strings, or quoted names"
  require (commands.map (·.source.number) == #[1, 2, 3, 4]) "wrong command numbers"
  require (commands.map (fun c => (c.source.span.start.line, c.source.span.start.column)) ==
    #[(2, 1), (3, 3), (4, 1), (6, 15)]) "wrong command start locations"
  require (commands[0]!.source.span.start.offset == 8) "UTF-8 offset counted characters"
  let span := commands[2]!.source.span
  require (span.stop.line == 6 && span.stop.column == 14) "wrong exclusive end location"
  for command in commands do
    let span := command.source.span
    require (String.fromUTF8! (input.toUTF8.extract span.start.offset span.stop.offset) == command.text)
      "source byte range does not recover the original command"
  require (eof.offset == input.utf8ByteSize) "reader did not consume trailing comments"
  -- A backslash is ordinary string content, even immediately before the closing quote.
  let backslash := "(set-info :source \"slash" ++ "\\" ++ "\")"
  let (commands, _) ← readAll (backslash ++ "(check-sat)")
  require (commands.map (·.text) == #[backslash, "(check-sat)"]) "incorrect backslash escape"
  let (commands, _) ← readAll "(echo \"λ🙂\")(check-sat)"
  let start := commands[1]!.source.span.start
  require (start.offset == 15 && start.column == 12) "UTF-8 bytes and character columns were conflated"
  let (commands, eof) ← readAll "; comment\r; another\n\t"
  require (commands.isEmpty && eof.line == 3 && eof.column == 2) "wrong empty-input location"
  for (input, reason) in #[
    (")", "expected '('"), ("symbol", "expected '('"),
    ("(assert\n true", "unterminated command opened at 1:1"),
    ("(set-info :source \"abc", "unterminated string"),
    ("(declare-const |abc", "unterminated quoted identifier"),
    ("(declare-const |a\\b| Bool)", "backslash is not allowed")
  ] do
    match ({} : Reader input).next "bad.smt2" with
    | .ok _ => throw (IO.userError s!"accepted malformed source: {input}")
    | .error error =>
      require (error.message.contains reason) s!"wrong source error: {repr error}"
      if input == "(assert\n true" then
        require (error.position.line == 2 && error.position.column == 6)
          "unterminated command did not identify EOF"
  IO.println "Source reader passed: exact bytes, quoting, UTF-8, line endings, and malformed input"
