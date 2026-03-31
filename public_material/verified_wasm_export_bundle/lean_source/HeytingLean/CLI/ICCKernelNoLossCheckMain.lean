import Lean
import Lean.Data.Json
import Std.Data.HashMap
import HeytingLean.LoF.ICCKernel.Faithfulness
import HeytingLean.Util.ModuleOwner

/-!
# `icc_kernel_no_loss_check`

Check recover-and-recheck closure for ICCKernel exports over a selected Lean environment.
-/

namespace HeytingLean
namespace CLI
namespace ICCKernelNoLossCheckMain

open Lean
open HeytingLean.LoF.ICCKernel
open HeytingLean.LoF.ICCKernel.Lower

structure CliArgs where
  outPath : System.FilePath := "icc_kernel_no_loss_report.json"
  modules : Array Lean.Name := #[]
  moduleFile : Option System.FilePath := none
  importModules : Array Lean.Name := #[]
  importModuleFile : Option System.FilePath := none
  modulePrefixes : Array String := #[]
  exactModuleFilter : Bool := false
  namePrefixes : Array String := #[]
  includeDefs : Bool := true
  declSkip : Nat := 0
  declTake : Option Nat := none
  deriving Inhabited

structure Failure where
  moduleName : String
  declName : String
  declKind : String
  stage : String
  message : String
  deriving Repr, Inhabited, ToJson

structure ModuleReport where
  moduleName : String
  declsSeen : Nat
  declsChecked : Nat
  failures : Nat
  deriving Repr, Inhabited, ToJson

structure Report where
  ok : Bool
  moduleRoots : Array String
  modulesChecked : Nat
  declsSeen : Nat
  declsChecked : Nat
  failuresCount : Nat
  moduleReports : Array ModuleReport
  failures : Array Failure
  deriving Repr, Inhabited, ToJson

private def usage : String :=
  String.intercalate "\n"
    [ "icc_kernel_no_loss_check - verify recover-and-recheck closure for ICCKernel exports"
    , ""
    , "Usage:"
    , "  lake exe icc_kernel_no_loss_check -- --module HeytingLean.LoF.ICCKernel.Faithfulness --exact-module-filter"
    , ""
    , "Options:"
    , "  --out <path>"
    , "  --module <Module.Name>"
    , "  --module-file <path>"
    , "  --import-module <Module.Name>"
    , "  --import-module-file <path>"
    , "  --module-prefix <prefix>"
    , "  --exact-module-filter"
    , "  --name-prefix <prefix>"
    , "  --include-defs | --no-include-defs"
    , "  --decl-skip <n>"
    , "  --decl-take <n>"
    ]

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
  | "--import-module" :: m :: rest => parseArgs rest { cfg with importModules := cfg.importModules.push (parseModuleName m) }
  | "--import-module-file" :: path :: rest => parseArgs rest { cfg with importModuleFile := some path }
  | "--module-prefix" :: p :: rest => parseArgs rest { cfg with modulePrefixes := cfg.modulePrefixes.push p }
  | "--exact-module-filter" :: rest => parseArgs rest { cfg with exactModuleFilter := true }
  | "--name-prefix" :: p :: rest => parseArgs rest { cfg with namePrefixes := cfg.namePrefixes.push p }
  | "--include-defs" :: rest => parseArgs rest { cfg with includeDefs := true }
  | "--no-include-defs" :: rest => parseArgs rest { cfg with includeDefs := false }
  | "--decl-skip" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with declSkip := v }
      | none => throw s!"invalid Nat for --decl-skip: {n}"
  | "--decl-take" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { cfg with declTake := some v }
      | none => throw s!"invalid Nat for --decl-take: {n}"
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

private def resolveNamedModules (mods : Array Lean.Name) (file? : Option System.FilePath) : IO (Array Lean.Name) := do
  let mut modules := mods
  if let some mf := file? then
    let lines ← IO.FS.lines mf
    for ln in lines do
      let s := ln.trim
      if !(s.isEmpty || s.startsWith "#") then
        modules := modules.push (parseModuleName s)
  pure <| modules.qsort (fun a b => a.toString < b.toString)

private def resolveModules (args : CliArgs) : IO (Array Lean.Name) :=
  resolveNamedModules args.modules args.moduleFile

private def resolveImportModules (args : CliArgs) : IO (Array Lean.Name) := do
  let imports ← resolveNamedModules args.importModules args.importModuleFile
  if imports.isEmpty then
    resolveModules args
  else
    pure imports

private def resolveFilterRoots (args : CliArgs) : IO (Array Lean.Name) := do
  let mut modules := args.modules
  if let some mf := args.moduleFile then
    let lines ← IO.FS.lines mf
    for ln in lines do
      let s := ln.trim
      if !(s.isEmpty || s.startsWith "#") then
        modules := modules.push (parseModuleName s)
  pure <| modules.qsort (fun a b => a.toString < b.toString)

private def moduleFor (env : Environment) (n : Lean.Name) : Lean.Name :=
  HeytingLean.Util.moduleOwnerOf env n

private def matchesAnyPrefix (s : String) (prefixes : Array String) : Bool :=
  prefixes.isEmpty || prefixes.any (fun p => s.startsWith p)

private def shouldKeep (env : Environment) (roots : Array String) (n : Lean.Name) (ci : Lean.ConstantInfo)
    (args : CliArgs) : Bool :=
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

private def sameStruct [BEq α] (a b : α) : Bool :=
  a == b

abbrev ModuleMap := Std.HashMap String (Lean.Name × Array Lean.ConstantInfo)

private def pushModuleConst (mods : ModuleMap) (moduleName : Lean.Name) (ci : Lean.ConstantInfo) : ModuleMap :=
  let key := moduleName.toString
  match mods.get? key with
  | some (m, cs) => mods.insert key (m, cs.push ci)
  | none => mods.insert key (moduleName, #[ci])

private def mkFailure (moduleName : Lean.Name) (ci : Lean.ConstantInfo) (stage message : String) : Failure :=
  { moduleName := moduleName.toString
    declName := ci.name.toString
    declKind := lowerConstantInfoCore ci |>.kindTag
    stage := stage
    message := message }

private def checkOneConstant (env : Environment) (moduleName : Lean.Name) (ci : Lean.ConstantInfo) :
    Nat × Array Failure :=
  match lowerConstantInfo ci with
  | .error err =>
      (0, #[mkFailure moduleName ci "lower" (reprStr err)])
  | .ok lowered =>
      match Raise.raiseConstantInfo lowered with
      | .error err =>
          (1, #[mkFailure moduleName ci "raise" (reprStr err)])
      | .ok recovered =>
          match lowerConstantInfo recovered with
          | .error err =>
              (1, #[mkFailure moduleName ci "re-lower" (reprStr err)])
          | .ok relowered =>
              Id.run do
                let mut failures : Array Failure := #[]
                if !sameStruct relowered lowered then
                  failures := failures.push (mkFailure moduleName ci "re-lower-mismatch" "re-lowered constant differs from exported lowering")
                if recovered.name != ci.name then
                  failures := failures.push (mkFailure moduleName ci "name-mismatch" "recovered declaration name differs from source")
                match env.find? recovered.name with
                | none =>
                    failures := failures.push (mkFailure moduleName ci "env-find" "recovered name not found in environment")
                | some resolved =>
                    match lowerConstantInfo resolved with
                    | .error err =>
                        failures := failures.push (mkFailure moduleName ci "env-re-lower" (reprStr err))
                    | .ok resolvedLowered =>
                        if !sameStruct resolvedLowered lowered then
                          failures := failures.push (mkFailure moduleName ci "env-mismatch" "environment-resolved constant differs from exported lowering")
                pure (1, failures)

private def checkModule (env : Environment) (moduleName : Lean.Name) (constants : Array Lean.ConstantInfo) :
    ModuleReport × Array Failure :=
  Id.run do
    let mut checked := 0
    let mut failures : Array Failure := #[]
    for ci in constants do
      let (count, localFailures) := checkOneConstant env moduleName ci
      checked := checked + count
      failures := failures ++ localFailures
    let bundle := lowerModuleBundleCore moduleName constants.toList
    match recoverAndRelowerModuleBundle bundle with
    | .error err =>
        let bundleFailure : Failure :=
          { moduleName := moduleName.toString
            declName := ""
            declKind := "bundle"
            stage := "bundle-recover"
            message := reprStr err }
        failures := failures.push bundleFailure
    | .ok recoveredBundle =>
        if !sameStruct recoveredBundle bundle then
          let bundleFailure : Failure :=
            { moduleName := moduleName.toString
              declName := ""
              declKind := "bundle"
              stage := "bundle-mismatch"
              message := "recovered module bundle differs from exported module bundle" }
          failures := failures.push bundleFailure
    ({ moduleName := moduleName.toString, declsSeen := constants.size, declsChecked := checked, failures := failures.size }, failures)

private def collectModules (env : Environment) (roots : Array String) (args : CliArgs) : ModuleMap :=
  Id.run do
    let mut mods : ModuleMap := {}
    for (n, ci) in env.constants do
      if shouldKeep env roots n ci args then
        mods := pushModuleConst mods (moduleFor env n) ci
    mods

private def sliceConstants (constants : Array Lean.ConstantInfo) (args : CliArgs) : Array Lean.ConstantInfo :=
  let dropped := constants.extract args.declSkip constants.size
  match args.declTake with
  | none => dropped
  | some take => dropped.extract 0 (Nat.min take dropped.size)

private def mkReport (env : Environment) (roots : Array String) (args : CliArgs) : Report :=
  Id.run do
    let grouped := collectModules env roots args
    let mut moduleReports : Array ModuleReport := #[]
    let mut failures : Array Failure := #[]
    let mut declsSeen := 0
    let mut declsChecked := 0
    let entries := grouped.toList.toArray.qsort (fun a b => a.fst < b.fst)
    for (_, (moduleName, constants)) in entries do
      let sliced := sliceConstants constants args
      let (moduleReport, localFailures) := checkModule env moduleName sliced
      moduleReports := moduleReports.push moduleReport
      failures := failures ++ localFailures
      declsSeen := declsSeen + moduleReport.declsSeen
      declsChecked := declsChecked + moduleReport.declsChecked
    { ok := failures.isEmpty
      moduleRoots := roots
      modulesChecked := moduleReports.size
      declsSeen := declsSeen
      declsChecked := declsChecked
      failuresCount := failures.size
      moduleReports := moduleReports
      failures := failures }

def mainImpl (argv : List String) : IO UInt32 := do
  let args ←
    match parseArgs argv with
    | .ok a => pure a
    | .error "help" =>
        IO.println usage
        return 0
    | .error e =>
        throw <| IO.userError e
  let filterRoots ← resolveFilterRoots args
  if filterRoots.isEmpty then
    throw <| IO.userError "no modules provided"
  let importModules ← resolveImportModules args
  setupSearchPath
  let env ← Lean.importModules (importModules.map (fun m => { module := m })) {}
  let roots := filterRoots.map Name.toString
  let report := mkReport env roots args
  IO.FS.writeFile args.outPath (Lean.toJson report).pretty
  IO.println s!"Wrote ICCKernel no-loss report to {args.outPath}"
  return if report.ok then 0 else 1

end ICCKernelNoLossCheckMain
end CLI
end HeytingLean

def main (argv : List String) : IO UInt32 :=
  HeytingLean.CLI.ICCKernelNoLossCheckMain.mainImpl argv
