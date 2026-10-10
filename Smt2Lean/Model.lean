import Smt2Lean.Translate
import Smt2Lean.SolverResponse

namespace Smt2Lean.Model

open Lean Meta

/-- Imported definitions are candidate interpretations, not proofs of a CHC system.
Missing/unsuccessful models have `definitions = none`, distinct from an empty model. -/
structure Response where
  status : Option SolverResponse.Status
  definitions : Option (Array ReconstructedDefinition)
  diagnostics : Array SolverResponse.Diagnostic
  deriving Inhabited

/-- Import one external check-sat/model response without calling a solver.
The existing parser checks definitions, then standalone reconstruction returns closed
Bool/Int values in `env`. Native parser objects cannot escape this call. Definitions
currently follow SMT script dependency order (helpers before their callers).
Malformed/unsupported models throw; solver errors and unknown reasons are returned
as diagnostics with no definitions. No declarations are added to the caller's env. -/
def importResponse (input : String) (env : Environment) (name : String := "solver-response")
    (maxRecDepth : Nat := 4096) : IO Response := do
  let response ← match SolverResponse.parse input name with
    | .ok response => pure response
    | .error message => throw (IO.userError message)
  let some definitions := response.model
    | return { status := response.status, definitions := none, diagnostics := response.diagnostics }
  let synthetic : Source.Ref := { file := name, number := 0, span := default }
  let sources := #[synthetic] ++ definitions.map (·.source) ++ #[synthetic]
  let script := "(set-logic ALL)\n" ++
    String.intercalate "\n" (definitions.map (·.text)).toList ++ "\n(check-sat)\n"
  let output ← IO.mkRef (none : Option (Array ReconstructedDefinition))
  (Backend.parseAndInspectSession script (name := name) (sources := sources) fun query => do
    let (values, _, _) ← (Translate.reconstructDefinitions query).toIO
      { fileName := name, fileMap := default, maxRecDepth,
        options := Lean.maxRecDepth.set {} maxRecDepth } { env }
    output.set (some values)
  ).runIO
  let some values ← output.get | throw (IO.userError s!"{name}: model import produced no result")
  return { status := response.status, definitions := some values, diagnostics := response.diagnostics }

end Smt2Lean.Model
