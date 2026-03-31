import Lean
import Lean.Data.Json
import HeytingLean.LoF.ICCKernel.Corpus
import HeytingLean.LoF.ICCKernel.Lower.Constant
import HeytingLean.Util.ModuleOwner

/-!
# `icc_kernel_corpus`

Build a retrieval-oriented corpus from ICCKernel-lowered declarations.
-/

namespace HeytingLean
namespace CLI
namespace ICCKernelCorpusMain

open Lean
open HeytingLean.LoF.ICCKernel
open HeytingLean.LoF.ICCKernel.Lower

structure CliArgs where
  outPath : System.FilePath := "icc_kernel_corpus.json"
  scopeLedgerOut : Option System.FilePath := none
  modules : Array Lean.Name := #[]
  moduleFile : Option System.FilePath := none
  modulePrefixes : Array String := #[]
  exactModuleFilter : Bool := false
  namePrefixes : Array String := #[]
  declSkip : Nat := 0
  maxDecls : Option Nat := none
  includeDefs : Bool := true
  deriving Inhabited

private def usage : String :=
  String.intercalate "\n"
    [ "icc_kernel_corpus - build an ICCKernel retrieval corpus"
    , ""
    , "Usage:"
    , "  lake exe icc_kernel_corpus -- --module HeytingLean --module-prefix HeytingLean --out icc_kernel_corpus.json"
    , ""
    , "Options:"
    , "  --out <path>"
    , "  --scope-ledger-out <path>"
    , "  --module <Module.Name>"
    , "  --module-file <path>"
    , "  --module-prefix <prefix>"
    , "  --exact-module-filter"
    , "  --name-prefix <prefix>"
    , "  --decl-skip <n>"
    , "  --max-decls <n>"
    , "  --include-defs | --no-include-defs"
    ]

private def parseNat? (s : String) : Option Nat :=
  s.toNat?

private def parseModuleName (s : String) : Lean.Name :=
  (s.splitOn ".").foldl (fun acc part => acc.mkStr part) Lean.Name.anonymous

private partial def parseArgs (args : List String) (cfg : CliArgs := default) : Except String CliArgs := do
  match args with
  | [] => pure cfg
  | "--" :: rest => parseArgs rest cfg
  | "--help" :: _ => throw "help"
  | "--out" :: path :: rest => parseArgs rest { cfg with outPath := path }
  | "--scope-ledger-out" :: path :: rest => parseArgs rest { cfg with scopeLedgerOut := some path }
  | "--module" :: m :: rest => parseArgs rest { cfg with modules := cfg.modules.push (parseModuleName m) }
  | "--module-file" :: path :: rest => parseArgs rest { cfg with moduleFile := some path }
  | "--module-prefix" :: p :: rest => parseArgs rest { cfg with modulePrefixes := cfg.modulePrefixes.push p }
  | "--exact-module-filter" :: rest => parseArgs rest { cfg with exactModuleFilter := true }
  | "--name-prefix" :: p :: rest => parseArgs rest { cfg with namePrefixes := cfg.namePrefixes.push p }
  | "--decl-skip" :: n :: rest =>
      match parseNat? n with
      | some v => parseArgs rest { cfg with declSkip := v }
      | none => throw s!"invalid Nat for --decl-skip: {n}"
  | "--max-decls" :: n :: rest =>
      match parseNat? n with
      | some v => parseArgs rest { cfg with maxDecls := some v }
      | none => throw s!"invalid Nat for --max-decls: {n}"
  | "--include-defs" :: rest => parseArgs rest { cfg with includeDefs := true }
  | "--no-include-defs" :: rest => parseArgs rest { cfg with includeDefs := false }
  | bad :: _ => throw s!"unknown arg: {bad}"

private partial def collectPackageLibs (root : System.FilePath) : IO (Array System.FilePath) := do
  let mut libs : Array System.FilePath := #[]
  if !(← root.pathExists) then
    return libs
  let direct := root / ".lake" / "build" / "lib" / "lean"
  if ← direct.pathExists then
    libs := libs.push direct
  if !(← root.isDir) then
    return libs
  for entry in (← root.readDir) do
    if ← entry.path.isDir then
      libs := libs ++ (← collectPackageLibs entry.path)
  return libs

private def setupSearchPath : IO Unit := do
  let sys ← Lean.findSysroot
  Lean.initSearchPath sys
  let cwd ← IO.currentDir
  let localLibCandidates : Array System.FilePath :=
    #[cwd / ".lake" / "build" / "lib" / "lean", cwd / ".." / ".lake" / "build" / "lib" / "lean"]
  let cur : Lean.SearchPath := (← Lean.searchPathRef.get)
  let mut sp := cur
  for localLib in localLibCandidates do
    if ← localLib.pathExists then
      sp := sp ++ [localLib]
  let pkgCandidates : Array System.FilePath := #[cwd / ".lake" / "packages", cwd / ".." / ".lake" / "packages"]
  for pkgsRoot in pkgCandidates do
    if ← pkgsRoot.pathExists then
      sp := sp ++ (← collectPackageLibs pkgsRoot).toList
  Lean.searchPathRef.set sp

private def moduleFor (env : Environment) (n : Lean.Name) : Lean.Name :=
  HeytingLean.Util.moduleOwnerOf env n

private def matchesAnyPrefix (s : String) (prefixes : Array String) : Bool :=
  prefixes.isEmpty || prefixes.any (fun p => s.startsWith p)

private def shouldKeep (env : Environment) (roots : Array String) (n : Lean.Name) (ci : Lean.ConstantInfo) (args : CliArgs) : Bool :=
  let nameStr := n.toString
  let moduleStr := (moduleFor env n).toString
  let moduleOk :=
    if args.exactModuleFilter then
      roots.any (· == moduleStr)
    else
      matchesAnyPrefix moduleStr args.modulePrefixes
  let kindOk :=
    args.includeDefs ||
      match ci with
      | .defnInfo _ => false
      | .opaqueInfo _ => false
      | _ => true
  kindOk && matchesAnyPrefix nameStr args.namePrefixes && moduleOk

private def resolveModules (args : CliArgs) : IO (Array Lean.Name) := do
  let mut modules := args.modules
  if let some mf := args.moduleFile then
    let lines ← IO.FS.lines mf
    for ln in lines do
      let s := ln.trim
      if !(s.isEmpty || s.startsWith "#") then
        modules := modules.push (parseModuleName s)
  pure <| modules.qsort (fun a b => a.toString < b.toString)

private def buildCorpus (env : Environment) (roots : Array String) (args : CliArgs) : CorpusBundle :=
  Id.run do
    let mut decls : Array ExportedDecl := #[]
    let mut total := 0
    for (n, ci) in env.constants do
      if shouldKeep env roots n ci args then
        total := total + 1
        let pastSkip := decide (args.declSkip < total)
        let withinBudget := (args.maxDecls.map (fun lim => decide (decls.size < lim))).getD true
        if pastSkip && withinBudget then
          match lowerConstantInfo ci with
          | .ok lowered =>
              decls := decls.push { moduleName := HeytingLean.LoF.ICCKernel.Name.ofLean (moduleFor env n), decl := lowered }
          | .error _ => pure ()
    let summary := exportSummaryOf roots total decls
    let rows := decls.map CorpusRow.ofExportedDecl
    { moduleRoots := roots, rows := rows, summary := summary }

private def ledgerJson (summary : ExportSummary) : Json :=
  Json.mkObj
    [ ("project", Json.str "lean_to_icc_kernel_memory_20260325")
    , ("module_roots", Json.arr (summary.moduleRoots.map Json.str))
    , ("decls_total", Json.num summary.declsTotal)
    , ("decls_supported", Json.num summary.declsSupported)
    , ("decls_unsupported", Json.num summary.declsUnsupported)
    , ("decls_unclassified", Json.num summary.declsUnclassified)
    , ("expr_constructor_counts",
        Json.arr <| summary.exprConstructorCounts.map (fun e => Json.mkObj [("label", Json.str e.label), ("count", Json.num e.count)]))
    , ("constant_kind_counts",
        Json.arr <| summary.constantKindCounts.map (fun e => Json.mkObj [("label", Json.str e.label), ("count", Json.num e.count)]))
    , ("last_updated", Json.str "generated_by_icc_kernel_corpus")
    ]

def mainImpl (argv : List String) : IO UInt32 := do
  let args ←
    match parseArgs argv with
    | .ok a => pure a
    | .error "help" =>
        IO.println usage
        return 0
    | .error e =>
        throw <| IO.userError e
  let modules ← resolveModules args
  if modules.isEmpty then
    throw <| IO.userError "no modules provided"
  setupSearchPath
  let env ← Lean.importModules (modules.map (fun m => { module := m })) {}
  let roots := modules.map Name.toString
  let bundle := buildCorpus env roots args
  IO.FS.writeFile args.outPath (Lean.toJson bundle).compress
  if let some ledger := args.scopeLedgerOut then
    IO.FS.writeFile ledger (ledgerJson bundle.summary).compress
  IO.println s!"Wrote ICCKernel corpus bundle to {args.outPath}"
  return 0

end ICCKernelCorpusMain
end CLI
end HeytingLean

def main (argv : List String) : IO UInt32 :=
  HeytingLean.CLI.ICCKernelCorpusMain.mainImpl argv
