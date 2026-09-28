import Smt2Lean.Translate

namespace Smt2Lean.Emit

open Lean Meta

/-- Render one file with statements first, followed by unfinished proofs. -/
def render (refutation : Expr) : MetaM String := do
  let body ← withOptions (fun options => options
      |>.setBool `pp.fullNames true
      |>.setBool `pp.deepTerms true
      |>.setBool `pp.proofs true
      -- Without annotations, a closed equality such as 1 = 2 defaults to Nat.
      |>.setBool `pp.numericTypes true
      |> (pp.maxSteps.set · 1000000)) do
    return (← ppExpr refutation).pretty
  if body.contains "⋯" then
    throwError "refutation is too large to print completely"
  let statements := "import Init\n\n-- Statements\n\n" ++
    "/-- No interpretation satisfies all assertions of the SMT query. -/\n" ++
    "def Refutation : Prop :=\n  " ++ body.replace "\n" "\n  " ++ "\n"
  let proofs := "\n-- Proofs\n\n" ++
    "-- Unfinished proof: replace sorry to establish the query's refutation.\n" ++
    "theorem refutation : Refutation := by\n  sorry\n"
  return statements ++ proofs

/-- Write Query.lean in a new directory. Existing destinations are refused. -/
def writeFile (output : System.FilePath) (source : String) : IO Unit := do
  try
    IO.FS.createDir output
  catch
    | .alreadyExists .. => throw (IO.userError s!"output already exists: {output}")
    | error => throw error
  IO.FS.writeFile (output / "Query.lean") source

end Smt2Lean.Emit
