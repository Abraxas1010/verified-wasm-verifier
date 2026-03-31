import Lean
import Lean.Data.Json
import HeytingLean.LoF.ICCKernel.Corpus
import HeytingLean.LoF.ICCKernel.Lower.Constant
import HeytingLean.Util.ModuleOwner

/-!
# `icc_kernel_export`

Export selected Lean declarations as ICCKernel JSON.
-/

namespace HeytingLean
namespace CLI
namespace ICCKernelExportMain

open Lean
open HeytingLean.LoF.ICCKernel
open HeytingLean.LoF.ICCKernel.Lower

structure CliArgs where
  outPath : System.FilePath := "icc_kernel_export.json"
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
    [ "icc_kernel_export - export Lean declarations into ICCKernel JSON"
    , ""
    , "Usage:"
    , "  lake exe icc_kernel_export -- --module HeytingLean --out icc_kernel_export.json"
    , "  lake exe icc_kernel_export -- --module-file modules.txt --module-prefix HeytingLean --out out.json"
    , ""
    , "Options:"
    , "  --out <path>"
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

private def scanDecls (env : Environment) (_moduleRoots : Array String) (args : CliArgs) : Array ExportedDecl × Nat :=
  Id.run do
    let mut decls : Array ExportedDecl := #[]
    let mut total := 0
    for (n, ci) in env.constants do
      if shouldKeep env _moduleRoots n ci args then
        total := total + 1
        let pastSkip := decide (args.declSkip < total)
        let withinBudget := (args.maxDecls.map (fun lim => decide (decls.size < lim))).getD true
        if pastSkip && withinBudget then
          match lowerConstantInfo ci with
          | .ok lowered =>
              decls := decls.push { moduleName := HeytingLean.LoF.ICCKernel.Name.ofLean (moduleFor env n), decl := lowered }
          | .error _ =>
              pure ()
    (decls, total)

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
  let (decls, total) := scanDecls env roots args
  let summary := exportSummaryOf roots total decls
  let bundle : ExportBundle := { moduleRoots := roots, declarations := decls, summary := summary }
  IO.FS.writeFile args.outPath (Lean.toJson bundle).compress
  IO.println s!"Wrote ICCKernel export bundle to {args.outPath}"
  return 0

end ICCKernelExportMain
end CLI
end HeytingLean

def main (argv : List String) : IO UInt32 :=
  HeytingLean.CLI.ICCKernelExportMain.mainImpl argv
