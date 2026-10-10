import Smt2Lean.Source

namespace Smt2Lean.SolverResponse

/-- Literal `check-sat` status, not a reachability/safety interpretation. -/
inductive Status where
  | sat | unsat | unknown
  deriving BEq, Repr, Inhabited

inductive DiagnosticKind where
  | error | reasonUnknown
  deriving BEq, Repr, Inhabited

structure Diagnostic where
  kind : DiagnosticKind
  message : String
  source : Source.Ref
  deriving Inhabited

/-- `none` is a missing model; `some #[]` is an explicitly empty model.
No status is inferred for a standalone model or an error-only response. -/
structure Parsed where
  status : Option Status := none
  model : Option (Array Source.Command) := none
  diagnostics : Array Diagnostic := #[]
  deriving Inhabited

private def failAt (form : Source.Command) (message : String) : Except String α :=
  .error s!"{form.source.context}: solver response: {message}"

private def forms (text name : String) (position : Source.Position := {})
    : Except String (Array Source.Command) := do
  let mut reader : Source.Reader text := { position }
  let mut result := #[]
  while true do
    let (form?, rest) ← (reader.nextResponse name).mapError fun error =>
      s!"{name}:{error.position.line}:{error.position.column}: solver response: {error.message}"
    reader := rest
    let some form := form? | return result
    result := result.push form
  return result

/-- Extract only a model's immediate definition lists, retaining source positions. -/
private def modelEntries (form : Source.Command) : Except String (Array Source.Command) := do
  let text := (form.text.drop 1 |>.dropEnd 1).toString
  let start := form.source.span.start
  let entries ← forms text form.source.file { start with offset := start.offset + 1, column := start.column + 1 }
  let entries := if entries[0]?.map (·.text) == some "model" then entries.extract 1 entries.size else entries
  return entries

private def checkDefinitions (entries : Array Source.Command) : Except String (Array Source.Command) := do
  let mut names : Array String := #[]
  let mut result := #[]
  for entry in entries do
    unless entry.tokens[0]? == some "(" && entry.tokens[1]? == some "define-fun" do
      failAt entry "models support ordinary define-fun entries only"
    let some name := entry.tokens[2]? | failAt entry "missing definition name"
    let name := if name.startsWith "|" then (name.drop 1 |>.dropEnd 1).toString else name
    if names.contains name then failAt entry s!"duplicate definition '{name}'"
    names := names.push name
    result := result.push { entry with source := { entry.source with number := result.size + 1 } }
  return result

private def messageText (token : String) : String :=
  if token.startsWith "\"" then (token.drop 1 |>.dropEnd 1).toString.replace "\"\"" "\"" else token

/-- Parse exactly one response, never discard trailing data. Accept `sat` plus a
bare definition list or `(model ...)`, standalone models, and direct define-fun
sequences. Status-only/error/unknown responses carry no definitions. `success`
acknowledgements may precede the response. Comments and quoted delimiters obey
SMT-LIB lexical rules. This handles check-sat models, not fixedpoint certificates. -/
def parse (input : String) (name : String := "solver-response") : Except String Parsed := do
  let entries ← forms input name
  let mut result : Parsed := {}
  let mut direct := false
  let mut sawResponse := false
  for form in entries do
    let status := match form.text with
      | "sat" => some Status.sat
      | "unsat" => some Status.unsat
      | "unknown" => some Status.unknown
      | _ => none
    if form.text == "success" then
      if sawResponse then failAt form "unexpected success after response"
    else if let some status := status then
      if sawResponse then failAt form "expected exactly one leading status"
      result := { result with status := some status }
      sawResponse := true
    else if form.tokens[1]? == some "error" then
      let #["(", "error", message, ")"] := form.tokens
        | failAt form "malformed error response"
      unless message.startsWith "\"" && message.endsWith "\"" do
        failAt form "error message must be a string"
      if result.model.isSome then failAt form "cannot combine a model with an error"
      result := { result with diagnostics := result.diagnostics.push {
        kind := .error, message := messageText message, source := form.source } }
      sawResponse := true
    else if form.tokens[1]? == some ":reason-unknown" then
      let #["(", ":reason-unknown", message, ")"] := form.tokens
        | failAt form "malformed reason-unknown response"
      unless result.status == some .unknown do failAt form "reason-unknown requires unknown status"
      if result.diagnostics.any (·.kind == .reasonUnknown) then failAt form "duplicate reason-unknown"
      if message == "(" || message == ")" then failAt form "malformed reason-unknown message"
      result := { result with diagnostics := result.diagnostics.push {
        kind := .reasonUnknown, message := messageText message, source := form.source } }
    else
      unless form.tokens[0]? == some "(" do failAt form s!"unexpected response atom '{form.text}'"
      if result.status == some .unsat || result.status == some .unknown then
        failAt form "a model requires sat status (fixedpoint query answers are unsupported)"
      unless result.diagnostics.isEmpty do failAt form "cannot combine a model with diagnostics"
      let isDirect := form.tokens[1]? == some "define-fun"
      if result.model.isSome && !(direct && isDirect) then failAt form "multiple or mixed model payloads"
      let definitions ← if isDirect then pure #[form] else modelEntries form
      result := { result with model := some (← checkDefinitions (result.model.getD #[] ++ definitions)) }
      direct := isDirect
      sawResponse := true
  unless sawResponse do throw s!"{name}: solver response: expected a status, model, or error"
  return result

end Smt2Lean.SolverResponse
