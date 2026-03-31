import Lean
import Lean.Data.Json
import Std
import HeytingLean.Embedding.ProofExtractor

namespace HeytingLean.Embedding

open Lean

structure CliArgs where
  outPath : System.FilePath := "proofs.json"
  modules : Array Name := #[]
  moduleFile : Option System.FilePath := none
  modulePrefixes : Array String := #[]
  namePrefixes : Array String := #[]
  maxTheorems : Option Nat := none
  maxNodes : Nat := 20000
  maxConstsPerDecl : Nat := 2000
  includeDefs : Bool := false
  includePretty : Bool := true
  prettyMaxChars : Nat := 4000
  deriving Inhabited

private def parseNat? (s : String) : Option Nat :=
  s.toNat?

private def parseModuleName (s : String) : Name :=
  (s.splitOn ".").foldl (fun acc part => acc.mkStr part) Name.anonymous

private def parseArgs (argv : List String) : Except String CliArgs := do
  let rec go (args : CliArgs) : List String → Except String CliArgs
    | [] => return args
    | "--" :: rest =>
      go args rest
    | "--out" :: p :: rest =>
      go { args with outPath := p } rest
    | "--module" :: m :: rest =>
      go { args with modules := args.modules.push (parseModuleName m) } rest
    | "--module-file" :: p :: rest =>
      go { args with moduleFile := some p } rest
    | "--module-prefix" :: p :: rest =>
      go { args with modulePrefixes := args.modulePrefixes.push p } rest
    | "--name-prefix" :: p :: rest =>
      go { args with namePrefixes := args.namePrefixes.push p } rest
    | "--max-theorems" :: n :: rest =>
      match parseNat? n with
      | none => throw s!"invalid Nat for --max-theorems: {n}"
      | some 0 => go { args with maxTheorems := none } rest
      | some v => go { args with maxTheorems := some v } rest
    | "--max-nodes" :: n :: rest =>
      match parseNat? n with
      | none => throw s!"invalid Nat for --max-nodes: {n}"
      | some v => go { args with maxNodes := v } rest
    | "--max-consts-per-decl" :: n :: rest =>
      match parseNat? n with
      | none => throw s!"invalid Nat for --max-consts-per-decl: {n}"
      | some v => go { args with maxConstsPerDecl := v } rest
    | "--include-defs" :: rest =>
      go { args with includeDefs := true } rest
    | "--pretty-max-chars" :: n :: rest =>
      match parseNat? n with
      | none => throw s!"invalid Nat for --pretty-max-chars: {n}"
      | some v => go { args with prettyMaxChars := v } rest
    | "--no-pretty" :: rest =>
      go { args with includePretty := false } rest
    | "--help" :: _ =>
      throw "help"
    | bad :: _ =>
      throw s!"unknown arg: {bad}"
  go {} argv

private def usage : String :=
  String.intercalate "\n"
    [ "proof2vec_extract --out <path> [--module <Module.Name> ...] [--module-file <path>] [--module-prefix <prefix> ...] [--name-prefix <prefix> ...]"
    , "               [--max-theorems N] [--max-nodes N] [--max-consts-per-decl N] [--include-defs] [--pretty-max-chars N] [--no-pretty]"
    , ""
    , "Notes:"
    , "- If neither --module nor --module-file is provided, extraction is a no-op and the tool exits nonzero."
    , "- Prefer importing a small set of HeytingLean modules to keep extraction fast."
    ]

private def setupSearchPath : IO Unit := do
  let sys ← Lean.findSysroot
  Lean.initSearchPath sys
  -- Mirror `HeytingLean.CLI.EnvList` so `lake exe` works from repo root.
  let cwd ← IO.currentDir
  let localLib : System.FilePath := cwd / ".." / "lean" / ".lake" / "build" / "lib" / "lean"
  let cur : Lean.SearchPath := (← Lean.searchPathRef.get)
  let mut sp := cur ++ [localLib]
  let basePkgs := #["mathlib","batteries","proofwidgets","Qq","aesop","importGraph","LeanSearchClient","plausible","Cli"]
  for nm in basePkgs do
    let lib := cwd / ".." / "lean" / ".lake" / "packages" / nm / ".lake" / "build" / "lib" / "lean"
    if ← lib.pathExists then
      sp := sp ++ [lib]
  -- Add all package build libs so cross-package extraction works.
  let pkgsRoot := cwd / ".." / "lean" / ".lake" / "packages"
  if ← pkgsRoot.pathExists then
    for entry in (← pkgsRoot.readDir) do
      let lib := entry.path / ".lake" / "build" / "lib" / "lean"
      if ← lib.pathExists then
        sp := sp ++ [lib]
  Lean.searchPathRef.set sp

def main (argv : List String) : IO UInt32 := do
  let args ←
    match parseArgs argv with
    | .ok a => pure a
    | .error "help" =>
      IO.eprintln usage
      return 0
    | .error e =>
      IO.eprintln e
      IO.eprintln usage
      return 2
  setupSearchPath
  let mut modules := args.modules
  if let some mf := args.moduleFile then
    let lines ← IO.FS.lines mf
    for ln in lines do
      let s := ln.trim
      if s.isEmpty then
        continue
      if s.startsWith "#" then
        continue
      modules := modules.push (parseModuleName s)
  if modules.isEmpty then
    IO.eprintln "no --module or --module-file provided; nothing to import/extract"
    return 2

  /-
  Importing many modules into a single environment can fail in this repo due to
  accidental global-name collisions in CLI/demo modules (e.g. multiple `main`).
  To make extraction robust, import each module into a fresh environment and
  extract only declarations defined in that exact module.
  -/
  let modsSorted := modules.qsort (fun a b => a.toString < b.toString)
  let total ← IO.FS.withFile args.outPath .write fun h => do
    h.putStr "["
    let mut first := true
    let mut remaining : Option Nat := args.maxTheorems
    let mut total : Nat := 0
    for m in modsSorted do
      if let some r := remaining then
        if r == 0 then
          break
      let env ← Lean.importModules #[{ module := m }] {}
      let maxForThis : Option Nat :=
        match remaining with
        | none => none
        | some r => some r
      let opts : ExtractOptions :=
        { modulePrefixes := args.modulePrefixes
          namePrefixes := args.namePrefixes
          onlyModule := some m
          maxTheorems := maxForThis
          maxNodes := args.maxNodes
          maxConstsPerDecl := args.maxConstsPerDecl
          includeDefs := args.includeDefs }
      -- Run extraction in CoreM so we can pretty-print `Expr` using `PrettyPrinter`.
      let coreCtx : Core.Context :=
        { fileName := "<proof2vec_extract>"
          fileMap := default
          currNamespace := Name.anonymous
          openDecls := [] }
      let coreState : Core.State := { env := env }
      let (arr, _) ← (extractAllTheorems opts args.includePretty args.prettyMaxChars).toIO coreCtx coreState
      for j in arr do
        if first then
          first := false
        else
          h.putStr ","
        h.putStr "\n"
        h.putStr (toString j)
      total := total + arr.size
      remaining := remaining.map (fun r => r - arr.size)
    if !first then
      h.putStr "\n"
    h.putStr "]\n"
    return total
  IO.println s!"Exported {total} declarations to {args.outPath}"
  return 0

end HeytingLean.Embedding

def main (argv : List String) : IO UInt32 :=
  HeytingLean.Embedding.main argv
