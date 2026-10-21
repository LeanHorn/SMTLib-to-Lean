import Smt2Lean
import Smt2Lean.Project

open Lean
open Smt2Lean

private def usage : String :=
  "Usage: smt2lean <input.smt2|input-directory> --out <new-directory> [--max-rec-depth N] [--mode auto|chc|model|fixedpoint] [--layout structured|inline] [--check-equivalence]\n" ++
  "       smt2lean --help\n\n" ++
  "Translate every check-sat/check-sat-assuming in a supported SMT-LIB session into Query.lean.\n" ++
  "Directory input writes <out>/<input-directory-name>/<relative-path>.lean and manifest.json.\n" ++
  "Names and subdirectories are preserved; unsafe name characters are normalized and collisions rejected.\n" ++
  "Each generated module has its own namespace. Individual translation failures are recorded; remaining files continue.\n" ++
  "Supports Bool, Int, Real, BitVec, arrays, monomorphic datatype constructors, and uninterpreted sorts and ground sort-constructor applications.\n" ++
  "Recursive definitions become function interpretations constrained by their defining equations.\n" ++
  "Real output imports the pinned Mathlib; other output uses Lean core.\n" ++
  "Supports push/pop, resets, and global declarations; statements precede proof templates.\n" ++
  "HORN logic generates Problem (model existence); other supported logics generate Refutation.\n" ++
  "--mode chc validates Horn clauses regardless of the declared logic; unsupported inputs are rejected.\n" ++
  "--layout inline puts CHC clauses directly inside Problem/Safe, preserving lets and source definitions (default: structured).\n" ++
  "--mode model preserves general formulas as model existence (outside Flex).\n" ++
  "--mode fixedpoint accepts positive Z3 rules and relation-name queries over Bool/Int/Real/BitVec.\n" ++
  "Fixedpoint output presents Safe (query unsat) and Reachable (query sat).\n" ++
  "Permitted result requests are recorded as unexecuted comments; no solver is run.\n" ++
  "The output directory must be new, and its parent must exist.\n" ++
  s!"--max-rec-depth sets the recursion limit during translation and in generated Lean (positive integer; default: {Emit.defaultMaxRecDepth}).\n" ++
  "--check-equivalence also proves equivalence between expanded and structured Lean statements (off by default); statement kernel checking is always enabled.\n" ++
  "The proof template contains sorry and must be completed in Lean."

private def parseArgs : List String → Option (String × String × Nat × Pipeline.Mode × Bool × Emit.Layout)
  | input :: rest => do
    let mut output := none
    let mut depth := none
    let mut mode := none
    let mut layout := none
    let mut checkEquivalence := false
    let mut args := rest
    while !args.isEmpty do
      let flag :: tail := args | none
      args := tail
      if flag == "--check-equivalence" then
        guard (!checkEquivalence)
        checkEquivalence := true
        continue
      let value :: tail := args | none
      args := tail
      match flag with
      | "--out" =>
        guard output.isNone
        output := some value
      | "--max-rec-depth" =>
        guard depth.isNone
        let n ← value.toNat?
        guard (n > 0)
        depth := some n
      | "--mode" =>
        guard mode.isNone
        mode := some (← match value with
          | "auto" => some Pipeline.Mode.auto
          | "chc" => some Pipeline.Mode.chc
          | "model" => some Pipeline.Mode.model
          | "fixedpoint" => some Pipeline.Mode.fixedpoint
          | _ => none)
      | "--layout" =>
        guard layout.isNone
        layout := some (← match value with
          | "structured" => some Emit.Layout.structured
          | "inline" => some Emit.Layout.inline
          | _ => none)
      | _ => none
    return (input, ← output, depth.getD Emit.defaultMaxRecDepth, mode.getD .auto, checkEquivalence,
      layout.getD .structured)
  | _ => none

private def translate (input output : System.FilePath) (maxRecDepth : Nat) (mode : Pipeline.Mode)
    (checkEquivalence : Bool) (layout : Emit.Layout) : IO Bool := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules #[{ module := `Smt2Lean.Translate }] {} (loadExts := true)
  if ← input.isDir then
    return ← Project.translate input output env maxRecDepth mode checkEquivalence layout
  let text ← IO.FS.readFile input
  let source ← Pipeline.translateSession text env input.toString maxRecDepth mode
    (checkEquivalence := checkEquivalence) (layout := layout)
  Emit.writeFile output source
  IO.println s!"Generated {output / "Query.lean"}"
  IO.println "Proof unfinished: replace sorry in the Proofs section of Query.lean."
  return true

def main (args : List String) : IO UInt32 := do
  if args == ["--help"] then
    IO.println usage
    return 0
  match parseArgs args with
  | some (input, output, maxRecDepth, mode, checkEquivalence, layout) =>
    if input.isEmpty || output.isEmpty || input.startsWith "-" || output.startsWith "-" then
      IO.eprintln usage
      return 2
    try
      return if ← translate input output maxRecDepth mode checkEquivalence layout then 0 else 1
    catch error =>
      IO.eprintln s!"smt2lean: {error}"
      return 1
  | _ =>
    IO.eprintln usage
    return 2
