import Smt2Lean.Pipeline

namespace Smt2Lean.Project

open Lean System

/-- Quoted Lean module components preserve spaces, dots, hyphens and keywords.
Only characters that cannot be quoted safely are replaced. Collisions are rejected. -/
private def fileName (name : String) : String :=
  let name := name.map fun c =>
    if c.toNat < 32 || c.toNat == 127 || c == '«' || c == '»' || c == '\\' then '_' else c
  if name.isEmpty then "Query" else name

private def qualified (parts : List String) : String :=
  String.intercalate "." (parts.map fun part => "«" ++ part ++ "»")

private def child (directory : FilePath) (name : String) : FilePath :=
  if directory.toString.isEmpty then name else directory / name

private structure Job where
  input : FilePath
  output : FilePath
  moduleName : String
  scope : String

/-- Enumerate before creating output; never follow links out of the input tree. -/
private def inputs (root : FilePath) : IO (Array FilePath) := do
  let mut pending : Array FilePath := #[""]
  let mut found := #[]
  while !pending.isEmpty do
    let relative := pending.back!
    pending := pending.pop
    for entry in ← (root / relative).readDir do
      let path := child relative entry.fileName
      match (← entry.path.symlinkMetadata).type with
      | .dir => pending := pending.push path
      | .file => if path.extension == some "smt2" then found := found.push path
      | .symlink => throw (IO.userError s!"symbolic links are unsupported in input directories: {root / path}")
      | .other => pure ()
  return found.qsort (fun a b => a.toString < b.toString)

/-- Check file/directory and case-insensitive collisions before writing anything. -/
private def plan (root : FilePath) (project : String) : IO (Array Job) := do
  let paths ← inputs root
  if paths.isEmpty then throw (IO.userError s!"no .smt2 files found in {root}")
  let mut seen : Std.HashMap String (String × Bool) := {}
  let mut jobs := #[]
  for input in paths do
    let dirs := input.components.dropLast
    let stem := fileName (input.fileStem.getD "")
    let components := project :: dirs.map fileName ++ [stem]
    let directory := (dirs.map fileName).foldl (· / ·) (FilePath.mk project)
    let output := directory / (stem ++ ".lean")
    let mut target : FilePath := project
    let mut original : FilePath := ""
    for dir in dirs do
      target := target / fileName dir
      original := child original dir
      let key := target.toString.toLower
      let identity := (original.toString, true)
      if let some previous := seen[key]? then
        unless previous == identity do
          throw (IO.userError s!"output name collision: {previous.1} and {original} map to {target}")
      seen := seen.insert key identity
    let key := output.toString.toLower
    if let some previous := seen[key]? then
      throw (IO.userError s!"output name collision: {previous.1} and {input} map to {output}")
    seen := seen.insert key (input.toString, false)
    jobs := jobs.push {
      input := input
      output := output
      moduleName := qualified components
      scope := qualified (["Smt2Lean", "Generated"] ++ components) }
  return jobs

private def writeAtomic (path temporary : FilePath) (text : String) : IO Unit := do
  try
    IO.FS.writeFile temporary text
    IO.FS.rename temporary path
  catch error =>
    try IO.FS.removeFile temporary catch _ => pure ()
    throw error

/-- Translate a project independently file by file. A failed input has a report entry
but no Lean file. Every translation starts from the same imported environment. -/
def translate (input output : FilePath) (env : Environment)
    (maxRecDepth : Nat) (mode : Pipeline.Mode) (checkEquivalence : Bool := false)
    (layout : Emit.Layout := .structured) : IO Bool := do
  let root ← IO.FS.realPath input
  let project := fileName (root.fileName.getD "Project")
  -- Reserve the report and scratch file outside the generated module tree.
  let project := if #["manifest.json", ".smt2lean.tmp"].contains project.toLower then
      project ++ "_project" else project
  let jobs ← plan root project
  try
    IO.FS.createDir output
  catch
    | .alreadyExists .. => throw (IO.userError s!"output already exists: {output}")
    | error => throw error
  let mut records : Array Json := #[]
  let mut failed := 0
  let mut translated := 0
  let temporary := output / ".smt2lean.tmp"
  for job in jobs do
    let start ← IO.monoMsNow
    let mut inputBytes : Option Nat := none
    let mut outputBytes : Option Nat := none
    let mut outputLines : Option Nat := none
    let mut failure : Option String := none
    let mut queries : Array Json := #[]
    try
      let text ← IO.FS.readFile (root / job.input)
      inputBytes := some text.utf8ByteSize
      let result ← Pipeline.translateSessionWithMetadata text env (root / job.input).toString maxRecDepth mode
        (some job.scope) checkEquivalence layout
      let source := result.source
      queries := result.queries
      let destination := output / job.output
      IO.FS.createDirAll (destination.parent.getD "")
      writeAtomic destination temporary source
      outputBytes := some source.utf8ByteSize
      outputLines := some ((source.splitOn "\n").length - 1)
      translated := translated + 1
      IO.println s!"Generated {destination}"
    catch error =>
      failed := failed + 1
      failure := some error.toString
      IO.eprintln s!"Failed {job.input}: {error}"
    records := records.push <| Json.mkObj [
      ("input", toJson job.input.toString), ("output", toJson job.output.toString),
      ("module", toJson job.moduleName), ("namespace", toJson job.scope),
      ("status", toJson (if failure.isSome then "failed" else "translated")),
      ("error", toJson failure), ("translation_ms", toJson ((← IO.monoMsNow) - start)),
      ("queries", toJson queries),
      ("input_bytes", toJson inputBytes), ("output_bytes", toJson outputBytes), ("output_lines", toJson outputLines)]
    let report := Json.mkObj [
      ("input_root", toJson root.toString), ("project", toJson project),
      ("total", toJson jobs.size), ("translated", toJson translated), ("failed", toJson failed),
      ("max_rec_depth", toJson maxRecDepth),
      ("check_equivalence", toJson checkEquivalence),
      ("mode", toJson (match mode with | .auto => "auto" | .chc => "chc" | .model => "model" | .fixedpoint => "fixedpoint")),
      ("layout", toJson (match layout with | .structured => "structured" | .inline => "inline")),
      ("files", toJson records)]
    writeAtomic (output / "manifest.json") temporary (report.pretty ++ "\n")
  IO.println s!"Translated {translated}/{jobs.size} files; {failed} failed. Report: {output / "manifest.json"}"
  IO.println "Generated proofs are unfinished; replace sorry in each file's Proofs section."
  return failed == 0

end Smt2Lean.Project
