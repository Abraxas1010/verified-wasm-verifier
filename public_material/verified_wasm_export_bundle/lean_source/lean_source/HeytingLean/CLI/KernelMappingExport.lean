import Lean
import Lean.Data.Json
import HeytingLean.CLI.Args
import HeytingLean.CLI.EnvBootstrap
import HeytingLean.CLI.ArbitraryLeanKernelBundle
import HeytingLean.LoF.ICC.Encoder.DeclWalker
import HeytingLean.LoF.LeanKernel.BundleCheck
import HeytingLean.LoF.LeanKernel.KernelMappingJson

open Lean
open System

namespace HeytingLean.CLI.KernelMappingExport

open HeytingLean.LoF.ICC.Encoder
open HeytingLean.LoF.LeanKernel

structure Args where
  modules : List String := []
  decls : List String := []
  since? : Option String := none
  output : Option FilePath := none
  limit? : Option Nat := none
  maxConsts : Nat := 8192
  deriving Inhabited

private def parseArg (xs : List String) (flag : String) : Option String :=
  match xs with
  | [] => none
  | x :: y :: rest => if x == flag then some y else parseArg (y :: rest) flag
  | _ => none

private def parseArgsMany (args : List String) (flag : String) : List String :=
  match args with
  | [] => []
  | x :: y :: rest =>
      if x = flag then
        y :: parseArgsMany rest flag
      else
        parseArgsMany (y :: rest) flag
  | _ => []

private def parseArgs (argv : List String) : Args :=
  let argv := HeytingLean.CLI.stripLakeArgs argv
  let modules := parseArgsMany argv "--module"
  let decls := parseArgsMany argv "--decl"
  let since? := parseArg argv "--since"
  let output := (parseArg argv "--output").map FilePath.mk
  let limit? := (parseArg argv "--limit").bind String.toNat?
  let maxConsts := (parseArg argv "--max-consts").bind String.toNat? |>.getD 8192
  { modules, decls, since?, output, limit?, maxConsts }

private def usage : String :=
  String.intercalate "\n"
    [ "kernel_mapping_export"
    , ""
    , "Export Lean-owned canonical/C/Rust/GPU mapping rows for staged kernel bundles."
    , ""
    , "Usage:"
    , "  lake env lean --run HeytingLean/CLI/KernelMappingExport.lean -- --decl HeytingLean.CLI.VerifierProofCorpus.applyId_eq_7"
    , "  lake env lean --run HeytingLean/CLI/KernelMappingExport.lean -- --module HeytingLean.CLI.VerifierProofCorpus --limit 4"
    , "  lake env lean --run HeytingLean/CLI/KernelMappingExport.lean -- --since origin/master"
    ]

private def modulesFromGitSince (gitRef : String) : IO (Except String (List String)) := do
  let out ← IO.Process.output {
    cmd := "git"
    args := #["diff", "--name-only", s!"{gitRef}..HEAD", "--", "lean"]
  }
  if out.exitCode ≠ 0 then
    return .error s!"git diff failed for --since {gitRef}: {out.stderr.trim}"
  let modules :=
    out.stdout.splitOn "\n"
      |>.map String.trim
      |>.filter (fun line => line.endsWith ".lean" && line.startsWith "lean/")
      |>.map (fun path =>
        let noPrefix := path.drop 5
        let noSuffix := noPrefix.dropRight 5
        noSuffix.replace "/" ".")
      |>.filter (· ≠ "")
      |>.eraseDups
  pure (.ok modules)

private def importEnv (modules : List String) : IO Environment := do
  HeytingLean.CLI.EnvBootstrap.bootstrapSearchPath
  let imports :=
    ([`Init] ++ modules.map HeytingLean.CLI.EnvBootstrap.moduleNameFromString).eraseDups
      |>.map (fun moduleName => { module := moduleName })
      |>.toArray
  importModules imports {}

private def dedupNames (names : List Name) : List Name :=
  let rec go (seen : Std.HashSet Name) (acc : List Name) : List Name → List Name
    | [] => acc.reverse
    | x :: xs =>
        if seen.contains x then
          go seen acc xs
        else
          go (seen.insert x) (x :: acc) xs
  go {} [] names

private def declModuleText? (declText : String) : Option String :=
  let parts := declText.splitOn "."
  match parts.reverse with
  | [] => none
  | [_] => none
  | _declName :: revModuleParts =>
      some <| ".".intercalate revModuleParts.reverse

private def moduleTargetDecls (env : Environment) (moduleText : String) : List Name :=
  let moduleName := HeytingLean.CLI.EnvBootstrap.moduleNameFromString moduleText
  (moduleDecls env moduleName).foldl (init := []) fun acc (declName, ci) =>
    if isSurfaceDecl env declName ci then
      declName :: acc
    else
      acc
  |>.reverse

private def resolveDecls (env : Environment) (args : Args) (moduleTexts : List String) : List Name :=
  let fromDecls := args.decls.map HeytingLean.CLI.EnvBootstrap.moduleNameFromString
  let resolved :=
    if !fromDecls.isEmpty then
      dedupNames fromDecls
    else
      let fromModules := moduleTexts.foldl (init := []) fun acc moduleText =>
        acc ++ moduleTargetDecls env moduleText
      dedupNames fromModules
  match args.limit? with
  | some limit => resolved.take limit
  | none => resolved

private def writeOutput (args : Args) (payload : Json) : IO Unit := do
  let text := payload.pretty
  match args.output with
  | some path =>
      IO.FS.writeFile path (text ++ "\n")
      IO.eprintln s!"[kernel_mapping_export] wrote {path}"
  | none =>
      IO.println text

private def errorRow (declName : Name) (err : String) : Json :=
  Json.mkObj
    [ ("decl_name", Json.str declName.toString)
    , ("status", Json.str "error")
    , ("error", Json.str err)
    ]

private def obligationResultToMappingVerdict (result : ObligationResult) : KernelVerdict :=
  match result.status with
  | .success => .matched
  | .blocked => .unsupported
  | .unsupported => .unsupported

private def overlayRowsWithCpuResults
    (rows : List KernelOverlayRow)
    (results : List ObligationResult) : List KernelOverlayRow :=
  let rec go : List KernelOverlayRow → List ObligationResult → List KernelOverlayRow
    | [], _ => []
    | row :: rows, [] => row :: rows
    | row :: rows, result :: results =>
        { row with cpuVerdict := obligationResultToMappingVerdict result } :: go rows results
  go rows results

private def artifactWithCpuResults
    (artifact : KernelMappingArtifact)
    (results : List ObligationResult) : KernelMappingArtifact :=
  { artifact with rows := overlayRowsWithCpuResults artifact.rows results }

private def bundleTablesJson (bundle : ArbitraryLeanKernelBundle) : Json :=
  Json.mkObj
    [ ("staged_name_table", Json.arr <| bundle.stagedNameTable.map Json.str)
    , ("staged_level_param_table", Json.arr <| bundle.stagedLevelParamTable.map Json.str)
    , ("staged_level_mvar_table", Json.arr <| bundle.stagedLevelMVarTable.map Json.str)
    , ("staged_expr_mvar_table", Json.arr <| bundle.stagedExprMVarTable.map Json.str)
    , ("nat_const_id", toJson bundle.natConstId)
    , ("string_const_id", toJson bundle.stringConstId)
    ]

private def checkSummaryJson (results : List ObligationResult) : Json :=
  let successCount := results.foldl (init := 0) fun acc result =>
    if result.status = .success then acc + 1 else acc
  let blockedCount := results.foldl (init := 0) fun acc result =>
    if result.status = .blocked then acc + 1 else acc
  let unsupportedCount := results.foldl (init := 0) fun acc result =>
    if result.status = .unsupported then acc + 1 else acc
  Json.mkObj
    [ ("row_count", toJson results.length)
    , ("success_count", toJson successCount)
    , ("blocked_count", toJson blockedCount)
    , ("unsupported_count", toJson unsupportedCount)
    ]

private def exportedRow
    (bundle : ArbitraryLeanKernelBundle)
    (results : List ObligationResult)
    (artifact : KernelMappingArtifact) : Json :=
  Json.mkObj
    [ ("status", Json.str "exported")
    , ("decl_name", Json.str bundle.declName)
    , ("module_name", Json.str bundle.moduleName)
    , ("decl_kind", Json.str bundle.declKind)
    , ("bundle_tables", bundleTablesJson bundle)
    , ("check_summary", checkSummaryJson results)
    , ("cpu_results", Json.arr <| results.toArray.map obligationResultToJson)
    , ("artifact", kernelMappingArtifactToJson artifact)
    ]

private def summaryJson (rows : Array Json) : Json :=
  let exported :=
    rows.foldl (init := 0) fun acc row =>
      match row.getObjValAs? String "status" with
      | .ok "exported" => acc + 1
      | _ => acc
  Json.mkObj
    [ ("row_count", toJson rows.size)
    , ("exported_count", toJson exported)
    , ("error_count", toJson (rows.size - exported))
    ]

def run (argv : List String) : IO UInt32 := do
  let args := parseArgs argv
  if args.modules.isEmpty && args.decls.isEmpty && args.since?.isNone then
    IO.eprintln usage
    return 1
  let sinceModules ←
    match args.since? with
    | some gitRef =>
        match ← modulesFromGitSince gitRef with
        | .ok modules => pure modules
        | .error err => IO.eprintln err; return 1
    | none => pure []
  let moduleTexts :=
    if !args.modules.isEmpty then
      (args.modules ++ sinceModules).eraseDups
    else
      let declModules :=
        if args.decls.isEmpty then
          []
        else
          args.decls.foldr (init := []) fun declText acc =>
            match declModuleText? declText with
            | some moduleText => moduleText :: acc
            | none => acc
      (args.modules ++ declModules ++ sinceModules).eraseDups
  if moduleTexts.isEmpty then
    IO.eprintln usage
    return 1
  let env ← importEnv moduleTexts
  let mut rows : Array Json := #[]
  for declName in resolveDecls env args moduleTexts do
    IO.eprintln s!"[kernel_mapping_export] exporting {declName}"
    match ← HeytingLean.CLI.ArbitraryLeanKernelBundle.exportKernelBundleForDecl env declName args.maxConsts with
    | .error err =>
        rows := rows.push (errorRow declName err)
    | .ok bundle =>
        let results := checkBundle bundle
        let canonicalRows := bundleToCanonicalRowsWithResults bundle results
        let artifact := artifactWithCpuResults (artifactOfCanonicalRows canonicalRows) results
        rows := rows.push (exportedRow bundle results artifact)
  let payload :=
    Json.mkObj
      [ ("tool", Json.str "kernel_mapping_export")
      , ("summary", summaryJson rows)
      , ("rows", Json.arr rows)
      ]
  writeOutput args payload
  pure 0

end HeytingLean.CLI.KernelMappingExport
