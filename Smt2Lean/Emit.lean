import Smt2Lean.Translate

namespace Smt2Lean.Emit

open Lean Meta

/-- Render a checked refutation and a separate, unfinished proof template. -/
def render (refutation : Expr) : MetaM (String × String) := do
  let body ← withOptions (fun options => options
      |>.setBool `pp.fullNames true
      |>.setBool `pp.deepTerms true
      |>.setBool `pp.proofs true
      |> (pp.maxSteps.set · 1000000)) do
    return (← ppExpr refutation).pretty
  if body.contains "⋯" then
    throwError "refutation is too large to print completely"
  let statements := "import Init\n\n" ++
    "/-- No interpretation satisfies all assertions of the SMT query. -/\n" ++
    "def Refutation : Prop :=\n  " ++ body.replace "\n" "\n  " ++ "\n"
  let proofs := "import Statements\n\n" ++
    "-- Unfinished proof: replace sorry to establish the query's refutation.\n" ++
    "theorem refutation : Refutation := by\n  sorry\n"
  return (statements, proofs)

/-- Create a new directory and write both files. Existing destinations are refused. -/
def writeFiles (output : System.FilePath) (statements proofs : String) : IO Unit := do
  try
    IO.FS.createDir output
  catch
    | .alreadyExists .. => throw (IO.userError s!"output already exists: {output}")
    | error => throw error
  IO.FS.writeFile (output / "Statements.lean") statements
  IO.FS.writeFile (output / "Proofs.lean") proofs

end Smt2Lean.Emit
