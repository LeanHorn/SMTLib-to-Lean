import Smt2Lean

open Lean
open Smt2Lean

private def usage : String :=
  "Usage: smt2lean <input.smt2> --out <new-directory>\n" ++
  "       smt2lean --help\n\n" ++
  "Translate one supported Bool/Int SMT-LIB query into Query.lean: statements, then proofs.\n" ++
  "The output directory must be new, and its parent must exist.\n" ++
  "The proof template contains sorry and must be completed in Lean."

private def translateFile (input output : System.FilePath) : IO Unit := do
  let text ← IO.FS.readFile input
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules #[{ module := `Smt2Lean.Translate }] {} (loadExts := true)
  (Backend.parseAndInspectQuery text (name := input.toString) fun query => do
    let translation : MetaM String := do
      Emit.render (← Translate.defineRefutation query)
    let (source, _, _) ← translation.toIO
      { fileName := input.toString, fileMap := default } { env }
    Emit.writeFile output source
  ).runIO
  IO.println s!"Generated {output / "Query.lean"}"
  IO.println "Proof unfinished: replace sorry in the Proofs section of Query.lean."

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--help"] =>
    IO.println usage
    return 0
  | [input, "--out", output] =>
    if input.isEmpty || output.isEmpty || input.startsWith "-" || output.startsWith "-" then
      IO.eprintln usage
      return 2
    try
      translateFile input output
      return 0
    catch error =>
      IO.eprintln s!"smt2lean: {error}"
      return 1
  | _ =>
    IO.eprintln usage
    return 2
