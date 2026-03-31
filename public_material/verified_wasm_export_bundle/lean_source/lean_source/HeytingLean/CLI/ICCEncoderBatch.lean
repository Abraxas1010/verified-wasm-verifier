import Lean
import Lean.Data.Json
import HeytingLean.CLI.Args
import HeytingLean.CLI.EnvBootstrap
import HeytingLean.LoF.ICC.Encoder.Annotate

open Lean
open System

namespace HeytingLean.CLI.ICCEncoderBatch

open HeytingLean.LoF.ICC.Encoder

structure Args where
  modules : List String := []
  decls : List String := []
  since? : Option String := none
  output : Option FilePath := none
  maxConsts : Nat := 8192
  maxNodes : Nat := 200000
  deriving Inhabited

def defaultModules : List String :=
  [ "HeytingLean.CLI.VerifierFixture"
  , "HeytingLean.CLI.VerifierProofCorpus"
  ]

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
  let maxConsts := (parseArg argv "--max-consts").bind String.toNat? |>.getD 8192
  let maxNodes := (parseArg argv "--max-nodes").bind String.toNat? |>.getD 200000
  { modules, decls, since?, output, maxConsts, maxNodes }

private def usage : String :=
  String.intercalate "\n"
    [ "icc_encoder_batch"
    , ""
    , "Declaration-backed Lean-to-ICC encoder batch report."
    , ""
    , "Usage:"
    , "  lake exe icc_encoder_batch -- --module HeytingLean.CLI.VerifierProofCorpus"
    , "  lake exe icc_encoder_batch -- --decl HeytingLean.CLI.VerifierProofCorpus.applyId_eq_7"
    , "  lake exe icc_encoder_batch -- --since origin/master"
    , ""
    , "Options:"
    , "  --module <Module.Name>   import and enumerate public checkable declarations (repeatable)"
    , "  --decl <Decl.Name>       inspect one declaration directly (repeatable)"
    , "  --since <git-ref>        enumerate changed Lean modules since <git-ref>"
    , "  --output <path>          write JSON report to file"
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

private def ownerModuleOfDeclText (declText : String) : String :=
  let parts := declText.splitOn "."
  match parts.reverse.drop 1 |>.reverse with
  | [] => declText
  | xs => String.intercalate "." xs

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
  if !fromDecls.isEmpty then
    dedupNames fromDecls
  else
    let fromModules := moduleTexts.foldl (init := []) fun acc moduleText =>
      acc ++ moduleTargetDecls env moduleText
    dedupNames fromModules

private def writeOutput (args : Args) (payload : Json) : IO Unit := do
  let text := payload.pretty
  match args.output with
  | some path =>
      IO.FS.writeFile path (text ++ "\n")
      IO.eprintln s!"[icc_encoder_batch] wrote {path}"
  | none =>
      IO.println text

private def summaryJson (rows : Array EncoderAnnotatedRow) : Json :=
  let tierACount := rows.foldl (init := 0) fun acc row =>
    acc + if row.classification.tier == .tierA then 1 else 0
  let tierBCount := rows.foldl (init := 0) fun acc row =>
    acc + if row.classification.tier == .tierB then 1 else 0
  let tierCCount := rows.foldl (init := 0) fun acc row =>
    acc + if row.classification.tier == .tierC then 1 else 0
  let encodedCount := rows.foldl (init := 0) fun acc row =>
    acc + if row.encoded?.isSome then 1 else 0
  let directLoweredCount := rows.foldl (init := 0) fun acc row =>
    acc + if row.directLowering.status == .success then 1 else 0
  let semanticGatedCount := rows.foldl (init := 0) fun acc row =>
    acc + if row.semanticGate.status == .success then 1 else 0
  let fullIngestionCount := rows.foldl (init := 0) fun acc row =>
    acc + if row.encoded?.isSome || row.directLowering.status == .success || row.classification.aggregateCatalogMatch then 1 else 0
  let divergenceCount := rows.foldl (init := 0) fun acc row =>
    acc + if row.encoded?.map (·.encodingDivergence) |>.getD false then 1 else 0
  let classifierBugCount := rows.foldl (init := 0) fun acc row =>
    acc + if row.classifierBug then 1 else 0
  let sizeRatios :=
    rows.foldl (init := ([] : List Float)) fun acc row =>
      match row.encoded? with
      | some payload =>
          match payload.positive.sizeRatio? with
          | some r => r :: acc
          | none => acc
      | none => acc
  let maxRatio :=
    sizeRatios.foldl (init := 0.0) fun acc r => if r > acc then r else acc
  Json.mkObj
    [ ("row_count", toJson rows.size)
    , ("tier_a_count", toJson tierACount)
    , ("tier_b_count", toJson tierBCount)
    , ("tier_c_count", toJson tierCCount)
    , ("encoded_count", toJson encodedCount)
    , ("direct_lowered_count", toJson directLoweredCount)
    , ("semantic_gated_count", toJson semanticGatedCount)
    , ("full_ingestion_count", toJson fullIngestionCount)
    , ("encoding_divergence_count", toJson divergenceCount)
    , ("classifier_bug_count", toJson classifierBugCount)
    , ("max_size_ratio", toJson maxRatio)
    ]

def main (argv : List String) : IO UInt32 := do
  let args := parseArgs argv
  if args.modules.isEmpty && args.decls.isEmpty && args.since?.isNone then
    let env ← importEnv defaultModules
    let mut rows : Array EncoderAnnotatedRow := #[]
    for declName in resolveDecls env { args with modules := defaultModules } defaultModules do
      match env.find? declName with
      | some ci =>
          rows := rows.push (← annotateDecl env declName ci args.maxConsts args.maxNodes)
      | none => pure ()
    let payload := Json.mkObj
      [ ("schema", Json.str "icc_encoder_batch_v1")
      , ("kind", Json.str "declaration_backed_icc_encoder_report")
      , ("target_scope", Json.str
          "full_lean_construct_support")
      , ("honest_boundary", Json.str
          "Target scope is full Lean construct support. Current implemented boundary now has three honest execution tiers: exact declaration-backed ICC witness translation; direct declaration-body staging into the staged kernel-expression plane; and a stronger staged-kernel semantic gate that requires local executable inference/checking over the staged dependency environment. Rows that fail the stronger gate remain visible as direct-ingestion-only rather than silently promoted.")
      , ("summary", summaryJson rows)
      , ("rows", Json.arr <| rows.map annotatedRowJson)
      ]
    writeOutput args payload
    return 0
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
          ["HeytingLean"]
      (args.modules ++ declModules ++ sinceModules).eraseDups
  if moduleTexts.isEmpty then
    IO.eprintln usage
    return 1
  let env ← importEnv moduleTexts
  let mut rows : Array EncoderAnnotatedRow := #[]
  for declName in resolveDecls env args moduleTexts do
    match env.find? declName with
    | some ci =>
        rows := rows.push (← annotateDecl env declName ci args.maxConsts args.maxNodes)
    | none => pure ()
  let payload := Json.mkObj
    [ ("schema", Json.str "icc_encoder_batch_v1")
    , ("kind", Json.str "declaration_backed_icc_encoder_report")
    , ("target_scope", Json.str
        "full_lean_construct_support")
    , ("honest_boundary", Json.str
        "Target scope is full Lean construct support. Current implemented boundary now has three honest execution tiers: exact declaration-backed ICC witness translation; direct declaration-body staging into the staged kernel-expression plane; and a stronger staged-kernel semantic gate that requires local executable inference/checking over the staged dependency environment. Rows that fail the stronger gate remain visible as direct-ingestion-only rather than silently promoted.")
    , ("input_modules", Json.arr <| moduleTexts.map Json.str |>.toArray)
    , ("input_decls", Json.arr <| args.decls.map Json.str |>.toArray)
    , ("since_ref", args.since?.map Json.str |>.getD Json.null)
    , ("summary", summaryJson rows)
    , ("rows", Json.arr <| rows.map annotatedRowJson)
    ]
  writeOutput args payload
  return 0

end HeytingLean.CLI.ICCEncoderBatch

def main := HeytingLean.CLI.ICCEncoderBatch.main
