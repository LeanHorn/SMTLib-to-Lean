import Smt2Lean.Source

namespace Smt2Lean.Backend.MatchWildcards

private inductive SExpr where
  | atom (text : String)
  | list (items : Array SExpr)
  deriving Inhabited

private partial def read (tokens : Array String) (start : Nat) : Except String (SExpr × Nat) := do
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

private partial def render : SExpr → String
  | .atom text => text
  | .list items => "(" ++ String.intercalate " " (items.toList.map render) ++ ")"

/-- No source name, including a quoted name, can capture a generated pattern variable. -/
def nameStem (tokens : Array String) : String := Id.run do
  let mut n := 0
  while tokens.any (fun token =>
      (if token.startsWith "|" then ((token.drop 1).dropEnd 1).toString else token)
        |>.startsWith s!"smt2lean.match.{n}.") do
    n := n + 1
  return s!"smt2lean.match.{n}."

private def wildcard (stem : String) (expr : SExpr) : StateM Nat SExpr := do
  match expr with
  | .atom "_" =>
    let n ← get
    modify (· + 1)
    return .atom s!"{stem}{n}"
  | _ => return expr

private partial def lower (stem : String) (expr : SExpr) : StateM Nat SExpr := do
  let .list items := expr | return expr
  if items.size == 3 && (match items[0]! with | .atom "match" => true | _ => false) then
    if let .list branches := items[2]! then
      let input ← lower stem items[1]!
      let branches ← branches.mapM fun branch => do
        let .list pair := branch | return branch
        unless pair.size == 2 do return branch
        let pattern ← match pair[0]! with
          | .list fields => do
            -- The first item is a constructor, never a wildcard or nested pattern.
            let tail ← (fields.extract 1 fields.size).mapM (wildcard stem)
            pure (.list (fields.extract 0 1 ++ tail))
          | atom => wildcard stem atom
        return .list #[pattern, ← lower stem pair[1]!]
      return .list #[items[0]!, input, .list branches]
  return .list (← items.mapM (lower stem))

/-- SMT-LIB 2.7 defines each pattern `_` as a fresh, unused variable.
Only adapt term-bearing commands; cvc5 still validates patterns, scopes and types. -/
def prepare (command : Source.Command) (stem : String) : Except String Source.Command := do
  unless #["assert", "define-fun", "define-const", "check-sat-assuming", "get-value"].contains
      (command.tokens[1]?.getD "") && command.tokens.contains "match" && command.tokens.contains "_" do
    return command
  let (expr, stop) ← read command.tokens 0
  unless stop == command.tokens.size do throw "unexpected trailing tokens"
  let text := render ((lower stem expr).run 0).1
  return { command with text, tokens := Source.tokenize text }

end Smt2Lean.Backend.MatchWildcards
