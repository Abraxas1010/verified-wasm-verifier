import Lean
import Lean.Data.Json
import HeytingLean.CLI.Args
import HeytingLean.CLI.EnvBootstrap
import HeytingLean.CLI.LeanExprJson
import HeytingLean.LoF.ICC.Encoder.Annotate

open Lean
open System

namespace HeytingLean.CLI.ArbitraryLeanSemanticBundle

open HeytingLean.LoF.ICC.Encoder

structure Args where
  modules : List String := []
  decls : List String := []
  since? : Option String := none
  output : Option FilePath := none
  limit? : Option Nat := none
  maxConsts : Nat := 8192
  maxNodes : Nat := 200000
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
  let maxNodes := (parseArg argv "--max-nodes").bind String.toNat? |>.getD 200000
  { modules, decls, since?, output, limit?, maxConsts, maxNodes }

private def usage : String :=
  String.intercalate "\n"
    [ "arbitrary_lean_semantic_bundle"
    , ""
    , "Arbitrary declaration bundle/check surface over the current staged kernel semantics."
    , ""
    , "Usage:"
    , "  lake env lean --run HeytingLean/CLI/ArbitraryLeanSemanticBundle.lean -- --module HeytingLean.CLI.VerifierProofCorpus"
    , "  lake env lean --run HeytingLean/CLI/ArbitraryLeanSemanticBundle.lean -- --decl HeytingLean.CLI.VerifierProofCorpus.applyId_eq_7"
    , "  lake env lean --run HeytingLean/CLI/ArbitraryLeanSemanticBundle.lean -- --since origin/master"
    , ""
    , "Options:"
    , "  --module <Module.Name>   import and enumerate public checkable declarations (repeatable)"
    , "  --decl <Decl.Name>       inspect one declaration directly (repeatable)"
    , "  --since <git-ref>        enumerate changed Lean modules since <git-ref>"
    , "  --output <path>          write JSON report to file"
    , "  --limit <n>              cap the number of declarations inspected after resolution"
    , "  --max-consts <n>         dependency closure cap (default: 8192)"
    , "  --max-nodes <n>          direct staged lowering heap cap (default: 200000)"
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

private def rawExportStatus (ci : ConstantInfo) : String :=
  if (constantValueExpr? ci).isSome then "type_and_value" else "type_only"

private def rawExportJson (ci : ConstantInfo) : Json :=
  Json.mkObj
    [ ("status", Json.str (rawExportStatus ci))
    , ("type_expr_json", HeytingLean.CLI.LeanExprJson.exprToJson ci.type)
    , ("value_expr_json", (constantValueExpr? ci).map HeytingLean.CLI.LeanExprJson.exprToJson |>.getD Json.null)
    ]

private def supportedSeedJson (row : EncoderAnnotatedRow) : Json :=
  match row.classification.supportedSeed? with
  | none => Json.null
  | some seed =>
      Json.mkObj
        [ ("source_id", Json.str seed.sourceId)
        , ("source_family", Json.str seed.sourceFamily)
        , ("common_source_id", Json.str (HeytingLean.LoF.ICC.mkCommonSourceId seed.sourceModuleName seed.sourceDeclName))
        , ("source_module_name", Json.str seed.sourceModuleName)
        , ("source_decl_name", Json.str seed.sourceDeclName)
        , ("proof_graph_module_name", Json.str seed.sourceModuleName)
        , ("proof_graph_decl_name", Json.str seed.sourceDeclName)
        , ("tags", Json.arr <| seed.tags.map Json.str |>.toArray)
        ]

private def bundleRowJson (ci : ConstantInfo) (row : EncoderAnnotatedRow) : Json :=
  Json.mkObj
    [ ("module_name", Json.str row.summary.moduleName.toString)
    , ("decl_name", Json.str row.summary.declName.toString)
    , ("decl_kind", Json.str row.summary.declKind)
    , ("proof_body_visible", Json.bool row.summary.proofBodyVisible)
    , ("closure_size", toJson row.summary.closure.size)
    , ("closure_overflow", Json.bool row.summary.closureOverflow)
    , ("direct_ref_count", toJson row.summary.directRefs.size)
    , ("missing_dep_count", toJson row.summary.missingDeps.size)
    , ("raw_export", rawExportJson ci)
    , ("tier", Json.str row.classification.tier.code)
    , ("classification_reason", Json.str row.classification.reason)
    , ("classification_detail", Json.str row.classification.detail)
    , ("supported_seed", supportedSeedJson row)
    , ("direct_lowering", directLoweringAttemptJson row.directLowering)
    , ("semantic_gate", semanticGateAttemptJson row.semanticGate)
    , ("semantic_supported", Json.bool (row.semanticGate.status == .success))
    , ("direct_lowering_supported", Json.bool (row.directLowering.status == .success))
    , ("encoder_annotation", annotatedRowJson row)
    ]

private def summaryJson (rows : Array (ConstantInfo × EncoderAnnotatedRow)) : Json :=
  let rowCount := rows.size
  let rawExportableCount := rowCount
  let semanticSupportedCount := rows.foldl (init := 0) fun acc (_, row) =>
    acc + if row.semanticGate.status == .success then 1 else 0
  let semanticBlockedCount := rows.foldl (init := 0) fun acc (_, row) =>
    acc + if row.semanticGate.status == .blocked then 1 else 0
  let semanticNAcount := rows.foldl (init := 0) fun acc (_, row) =>
    acc + if row.semanticGate.status == .notApplicable then 1 else 0
  let directSupportedCount := rows.foldl (init := 0) fun acc (_, row) =>
    acc + if row.directLowering.status == .success then 1 else 0
  let exactSeedCount := rows.foldl (init := 0) fun acc (_, row) =>
    acc + if row.classification.exactCatalogMatch then 1 else 0
  let aggregateSeedCount := rows.foldl (init := 0) fun acc (_, row) =>
    acc + if row.classification.aggregateCatalogMatch then 1 else 0
  Json.mkObj
    [ ("row_count", toJson rowCount)
    , ("raw_exportable_count", toJson rawExportableCount)
    , ("semantic_supported_count", toJson semanticSupportedCount)
    , ("semantic_blocked_count", toJson semanticBlockedCount)
    , ("semantic_not_applicable_count", toJson semanticNAcount)
    , ("direct_lowering_supported_count", toJson directSupportedCount)
    , ("exact_seed_match_count", toJson exactSeedCount)
    , ("aggregate_seed_match_count", toJson aggregateSeedCount)
    ]

private def writeOutput (args : Args) (payload : Json) : IO Unit := do
  let text := payload.pretty
  match args.output with
  | some path =>
      IO.FS.writeFile path (text ++ "\n")
      IO.eprintln s!"[arbitrary_lean_semantic_bundle] wrote {path}"
  | none =>
      IO.println text

def main (argv : List String) : IO UInt32 := do
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
  let mut rows : Array (ConstantInfo × EncoderAnnotatedRow) := #[]
  for declName in resolveDecls env args moduleTexts do
    IO.eprintln s!"[arbitrary_lean_semantic_bundle] annotating {declName}"
    match env.find? declName with
    | some ci =>
        let row ← annotateDecl env declName ci args.maxConsts args.maxNodes
        rows := rows.push (ci, row)
        IO.eprintln s!"[arbitrary_lean_semantic_bundle] finished {declName}"
    | none => pure ()
  let payload := Json.mkObj
    [ ("schema", Json.str "arbitrary_lean_semantic_bundle_v1")
    , ("kind", Json.str "arbitrary_declaration_semantic_bundle")
    , ("target_scope", Json.str "arbitrary_checkable_declarations_current_staged_kernel_support")
    , ("honest_boundary", Json.str
        "This surface exports arbitrary selected checkable Lean declarations together with staged semantic verdicts over the current local kernel support. It is not a claim of full arbitrary Lean verification, full GPU checking, or complete support for every Lean declaration shape.")
    , ("input_modules", Json.arr <| moduleTexts.map Json.str |>.toArray)
    , ("input_decls", Json.arr <| args.decls.map Json.str |>.toArray)
    , ("since_ref", args.since?.map Json.str |>.getD Json.null)
    , ("decl_limit", args.limit?.map toJson |>.getD Json.null)
    , ("summary", summaryJson rows)
    , ("rows", Json.arr <| rows.map (fun (ci, row) => bundleRowJson ci row))
    ]
  writeOutput args payload
  return 0

end HeytingLean.CLI.ArbitraryLeanSemanticBundle

def main := HeytingLean.CLI.ArbitraryLeanSemanticBundle.main
