import Lean
import Lean.Data.Json
import HeytingLean.Embedding.Telescope

namespace HeytingLean.Embedding

open Lean

structure CliArgs where
  decl : Option Name := none
  module : Option Name := none
  pairsFile : Option System.FilePath := none
  outPath : Option System.FilePath := none
  deriving Inhabited

private def parseModuleName (s : String) : Name :=
  (s.splitOn ".").foldl (fun acc part => acc.mkStr part) Name.anonymous

private def parseArgs (argv : List String) : Except String CliArgs := do
  let rec go (args : CliArgs) : List String → Except String CliArgs
    | [] => return args
    | "--" :: rest =>
      go args rest
    | "--decl" :: n :: rest =>
      go { args with decl := some (parseModuleName n) } rest
    | "--module" :: m :: rest =>
      go { args with module := some (parseModuleName m) } rest
    | "--pairs-file" :: p :: rest =>
      go { args with pairsFile := some p } rest
    | "--out" :: p :: rest =>
      go { args with outPath := some p } rest
    | "--help" :: _ =>
      throw "help"
    | bad :: _ =>
      throw s!"unknown arg: {bad}"
  go {} argv

private def usage : String :=
  String.intercalate "\n"
    [ "proof2vec_telescope --module <Module.Name> --decl <Decl.Name> [--out <path>]"
    , "proof2vec_telescope --pairs-file <path> [--out <path>]"
    , ""
    , "pairs-file format: one pair per line: <Module.Name> <Decl.Name>"
    ]

private def setupSearchPath : IO Unit := do
  let sys ← Lean.findSysroot
  Lean.initSearchPath sys
  let cwd ← IO.currentDir
  let localLib : System.FilePath := cwd / ".." / "lean" / ".lake" / "build" / "lib" / "lean"
  let cur : Lean.SearchPath := (← Lean.searchPathRef.get)
  let mut sp := cur ++ [localLib]
  let basePkgs := #["mathlib","batteries","proofwidgets","Qq","aesop","importGraph","LeanSearchClient","plausible","Cli"]
  for nm in basePkgs do
    let lib := cwd / ".." / "lean" / ".lake" / "packages" / nm / ".lake" / "build" / "lib" / "lean"
    if ← lib.pathExists then
      sp := sp ++ [lib]
  Lean.searchPathRef.set sp

private def binderJsonToJson (b : BinderJson) : Json :=
  Json.mkObj
    [ ("binder_info", b.binderInfo)
    , ("name", b.name)
    , ("type_pretty", b.typePretty)
    ]

private def telescopeJsonToJson (t : TelescopeJson) : Json :=
  Json.mkObj
    [ ("decl", t.decl)
    , ("binders", Json.arr (t.binders.map binderJsonToJson))
    , ("target_pretty", t.targetPretty)
    , ("is_prop", t.isProp)
    ]

private def extractOne (env : Environment) (decl : Name) : IO Json := do
  let coreCtx : Core.Context :=
    { fileName := "<proof2vec_telescope>"
      fileMap := default
      currNamespace := Name.anonymous
      openDecls := [] }
  let coreState : Core.State := { env := env }
  try
    let (tj, _) ← (getTelescopeJson decl).toIO coreCtx coreState
    return telescopeJsonToJson tj
  catch e =>
    return Json.mkObj [("decl", decl.toString), ("error", toString e)]

private def readPairs (path : System.FilePath) : IO (Array (Name × Name)) := do
  let lines ← IO.FS.lines path
  let mut out : Array (Name × Name) := #[]
  for ln in lines do
    let s := ln.trim
    if s.isEmpty || s.startsWith "#" then
      continue
    let parts := s.split (fun c => c == ' ' || c == '\t') |>.filter (fun t => !t.isEmpty)
    match parts with
    | modStr :: declStr :: _ =>
      out := out.push (parseModuleName modStr, parseModuleName declStr)
    | _ =>
      continue
  return out

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

  if let some pf := args.pairsFile then
    let pairs ← readPairs pf
    if pairs.isEmpty then
      IO.eprintln s!"empty pairs-file: {pf}"
      return 2
    -- Sort by module so each module is imported once.
    let pairsSorted := pairs.qsort (fun a b => a.fst.toString < b.fst.toString)
    let mut out : Array Json := #[]
    let mut curMod : Option Name := none
    let mut curEnv : Option Environment := none
    for (m, d) in pairsSorted do
      if curMod != some m then
        curMod := some m
        curEnv := some (← Lean.importModules #[{ module := m }] {})
      match curEnv with
      | none => pure ()
      | some env =>
        out := out.push (← extractOne env d)
    let j := Json.mkObj [("schema_version", 1), ("results", Json.arr out)]
    let txt := toString j
    match args.outPath with
    | some p => IO.FS.writeFile p txt
    | none => IO.println txt
    return 0

  match args.module, args.decl with
  | some m, some d =>
    let env ← Lean.importModules #[{ module := m }] {}
    let j ← extractOne env d
    let txt := toString j
    match args.outPath with
    | some p => IO.FS.writeFile p txt
    | none => IO.println txt
    return 0
  | _, _ =>
    IO.eprintln usage
    return 2

end HeytingLean.Embedding

def main (argv : List String) : IO UInt32 :=
  HeytingLean.Embedding.main argv
