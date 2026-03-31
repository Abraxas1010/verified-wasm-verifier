import Lean
import Lean.Data.Json
import HeytingLean.CLI.ArbitraryLeanKernelBundle
import HeytingLean.LoF.LeanKernel.BundleBlockers

open Lean
open System

namespace HeytingLean.CLI.ArbitraryLeanKernelBundleInventory

open HeytingLean.CLI.ArbitraryLeanKernelBundle
open HeytingLean.LoF.LeanKernel

private def resultStatusCounts (results : List ObligationResult) : Json :=
  let successCount := results.foldl (init := 0) fun acc result =>
    acc + if result.status == .success then 1 else 0
  let blockedCount := results.foldl (init := 0) fun acc result =>
    acc + if result.status == .blocked then 1 else 0
  let unsupportedCount := results.foldl (init := 0) fun acc result =>
    acc + if result.status == .unsupported then 1 else 0
  Json.mkObj
    [ ("success", toJson successCount)
    , ("blocked", toJson blockedCount)
    , ("unsupported", toJson unsupportedCount)
    ]

private def rowJson
    (declName : Name)
    (exported : Except String ArbitraryLeanKernelBundle)
    (fuel : Nat := 256) : Json :=
  match exported with
  | .error err =>
      Json.mkObj
        [ ("decl_name", Json.str declName.toString)
        , ("status", Json.str "export_error")
        , ("error", Json.str err)
        ]
  | .ok bundle =>
      let results := checkBundle bundle fuel
      let blockedResults := results.filter (·.status == .blocked)
      let unsupportedResults := results.filter (·.status == .unsupported)
      let supported := unsupportedResults.isEmpty
      let verified := supported && blockedResults.isEmpty
      Json.mkObj
        [ ("decl_name", Json.str bundle.declName)
        , ("module_name", Json.str bundle.moduleName)
        , ("decl_kind", Json.str bundle.declKind)
        , ("status", Json.str (if verified then "verified" else if supported then "blocked" else "unsupported"))
        , ("supported", Json.bool supported)
        , ("verified", Json.bool verified)
        , ("bundle", bundleToJson bundle)
        , ("obligations", Json.arr <| results.map obligationResultToJson |>.toArray)
        , ("status_counts", resultStatusCounts results)
        , ("blockers", Json.arr <| blockedResults.map blockerJson |>.toArray)
        , ("blocker_family_counts", Json.mkObj <| (blockerCounts blockedResults).toList.map fun (label, count) => (label, toJson count))
        ]

private def summaryJson (rows : Array Json) : Json :=
  let verifiedCount :=
    rows.foldl (init := 0) fun acc row =>
      match row.getObjValAs? Bool "verified" with
      | .ok true => acc + 1
      | _ => acc
  let supportedCount :=
    rows.foldl (init := 0) fun acc row =>
      match row.getObjValAs? Bool "supported" with
      | .ok true => acc + 1
      | _ => acc
  let unsupportedCount :=
    rows.foldl (init := 0) fun acc row =>
      match row.getObjValAs? String "status" with
      | .ok "unsupported" => acc + 1
      | _ => acc
  let blockedCount :=
    rows.foldl (init := 0) fun acc row =>
      match row.getObjValAs? String "status" with
      | .ok "blocked" => acc + 1
      | .ok "export_error" => acc + 1
      | _ => acc
  Json.mkObj
    [ ("row_count", toJson rows.size)
    , ("verified_supported_count", toJson verifiedCount)
    , ("supported_count", toJson supportedCount)
    , ("unsupported_count", toJson unsupportedCount)
    , ("blocked_count", toJson blockedCount)
    ]

private def writeOutput (args : Args) (payload : Json) : IO Unit := do
  let text := payload.pretty
  match args.output with
  | some path =>
      IO.FS.writeFile path (text ++ "\n")
      IO.eprintln s!"[arbitrary_lean_kernel_bundle_inventory] wrote {path}"
  | none =>
      IO.println text

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
    IO.eprintln s!"[arbitrary_lean_kernel_bundle_inventory] checking {declName}"
    let exported ← exportKernelBundleForDecl env declName args.maxConsts
    rows := rows.push (rowJson declName exported)
  let payload :=
    Json.mkObj
      [ ("tool", Json.str "arbitrary_lean_kernel_bundle_inventory")
      , ("summary", summaryJson rows)
      , ("rows", Json.arr rows)
      , ("honest_assessment",
          Json.str
            "This inventory reports exported kernel bundles plus CPU-staged obligation results for the selected declaration slice. Verified-supported rows exclude unsupported rows by construction, and blocked rows retain blocker-family labels.") ]
  writeOutput args payload
  pure 0

end HeytingLean.CLI.ArbitraryLeanKernelBundleInventory
