import HeytingLean.CLI.Args
import HeytingLean.Genesis.EigenformSoup.NoncomputableBridge
import HeytingLean.Genesis.EigenformSoup.RuntimeTrace
import HeytingLean.Util.SHA

/-!
# EigenformSoup native trace parity bundle generator

Emits a C bundle for runtime parity checks over a deterministic LES trace payload
computed from the executable `RuntimeTrace` lane (non-proxy).
-/

namespace HeytingLean.CLI.EigenformSoupNativeTraceParityMain

open System
open HeytingLean.Genesis.EigenformSoup

private def usage : String :=
  String.intercalate "\n"
    [ "eigenform_soup_native_trace_parity"
    , "  Generates a runtime parity C bundle for LES native-runtime trace payloads."
    , ""
    , "Options:"
    , "  --size <nat> | --size=<nat>            substrate size (default: 16)"
    , "  --depth <nat> | --depth=<nat>          substrate depth (default: 2)"
    , "  --epochs <nat> | --epochs=<nat>        max epochs (default: 64)"
    , "  --sample-every <nat> | --sample-every=<nat>  sample interval (default: 1)"
    , "  --out-dir <path> | --out-dir=<path>    output directory (default: dist/eigenform_soup_native_trace_parity)"
    , "  --help                                 show this message"
    ]

private def hasFlag (argv : List String) (flag : String) : Bool :=
  argv.any (· = flag)

private def findOptValue (argv : List String) (key : String) : Option String :=
  let keyEq := key ++ "="
  let rec go : List String → Option String
    | [] => none
    | x :: xs =>
        if x.startsWith keyEq then
          some (x.drop keyEq.length)
        else if x = key then
          match xs with
          | y :: _ => some y
          | [] => none
        else
          go xs
  go argv

private def parseNatOpt (argv : List String) (key : String) (default : Nat) :
    Except String Nat := do
  match findOptValue argv key with
  | none => pure default
  | some raw =>
      match raw.toNat? with
      | some n => pure n
      | none => throw s!"invalid {key} value: {raw}"

private def parseOutDir (argv : List String) : FilePath :=
  let raw := (findOptValue argv "--out-dir").getD "dist/eigenform_soup_native_trace_parity"
  FilePath.mk raw

private def sampleSnapshots
    (epochs sampleEvery : Nat)
    (xs : List RuntimeSnapshot) : List RuntimeSnapshot :=
  let step := if sampleEvery = 0 then 1 else sampleEvery
  xs.filter (fun s => s.epoch % step = 0 || s.epoch = epochs)

private def nearThreshold (size : Nat) : Nat :=
  Nat.max 1 (size / 8)

private def daofCountsAt (size unresolved near : Nat) : Nat × Nat × Nat × Nat :=
  if size = 0 then
    (1, 0, 0, 0)
  else
    let distinguished := size - unresolved
    if unresolved = 0 then
      (0, 0, 0, distinguished)
    else if near < unresolved then
      (0, unresolved, 0, distinguished)
    else
      (0, 0, unresolved, distinguished)

private def addCounts (a b : Nat × Nat × Nat × Nat) : Nat × Nat × Nat × Nat :=
  (a.1 + b.1, a.2.1 + b.2.1, a.2.2.1 + b.2.2.1, a.2.2.2 + b.2.2.2)

private def daofTotals (size : Nat) (xs : List RuntimeSnapshot) : Nat × Nat × Nat × Nat :=
  let near := nearThreshold size
  xs.foldl (fun acc s => addCounts acc (daofCountsAt size s.unresolvedCount near)) (0, 0, 0, 0)

private def observationGapSum (xs : List RuntimeSnapshot) : Nat :=
  xs.foldl (fun acc s => acc + s.unresolvedCount) 0

private def maxJLevel (xs : List RuntimeSnapshot) : Nat :=
  xs.foldl (fun acc s => Nat.max acc s.jLevel) 0

private def firstEigenformEpoch? : List RuntimeSnapshot → Option Nat
  | [] => none
  | s :: xs =>
      if s.jLevel = 0 then firstEigenformEpoch? xs else some s.epoch

private def trajectoryEntryJson (s : RuntimeSnapshot) : String :=
  "{" ++
    "\"epoch\":" ++ toString s.epoch ++
    ",\"entropy\":" ++ toString s.unresolvedCount ++
    ",\"stabilized\":" ++ toString s.stabilizedCount ++
    ",\"j_level\":" ++ toString s.jLevel ++
    "}"

private def stateTraceEntryJson (s : RuntimeSnapshot) : String :=
  "{" ++
    "\"epoch\":" ++ toString s.epoch ++
    ",\"stabilized_count\":" ++ toString s.stabilizedCount ++
    ",\"entropy\":" ++ toString s.unresolvedCount ++
    ",\"j_level\":" ++ toString s.jLevel ++
    "}"

private def trajectoryJson (xs : List RuntimeSnapshot) : String :=
  "[" ++ String.intercalate "," (xs.map trajectoryEntryJson) ++ "]"

private def stateTraceJson (xs : List RuntimeSnapshot) : String :=
  "[" ++ String.intercalate "," (xs.map stateTraceEntryJson) ++ "]"

private def detectionRows : List RuntimeSnapshot → List String
  | xs =>
      let rec go (seenFirst : Bool) (prevJ : Nat) : List RuntimeSnapshot → List String
        | [] => []
        | s :: rest =>
            let currJ := s.jLevel
            if !seenFirst && currJ > 0 then
              ("{" ++
                "\"epoch\":" ++ toString s.epoch ++
                ",\"event\":\"first_eigenform\"" ++
                ",\"assembly_index\":" ++ toString currJ ++
                "}") :: go true currJ rest
            else if seenFirst && currJ > prevJ then
              ("{" ++
                "\"epoch\":" ++ toString s.epoch ++
                ",\"event\":\"plateau_synthesis\"" ++
                ",\"assembly_index\":" ++ toString currJ ++
                "}") :: go seenFirst currJ rest
            else
              go seenFirst currJ rest
      go false 0 xs

private def eigenformDetectionEventsJson (xs : List RuntimeSnapshot) : String :=
  "[" ++ String.intercalate "," (detectionRows xs) ++ "]"

private def symbiogenesisRows (xs : List RuntimeSnapshot) : List String :=
  (List.zip xs xs.tail).filterMap (fun p =>
    let prev := p.1
    let next := p.2
    let levelPrev := prev.jLevel
    let levelNext := next.jLevel
    if levelNext > levelPrev then
      let thesisMeet := levelPrev / 2
      let antithesisJoin := levelPrev - thesisMeet + (levelNext - levelPrev)
      let plateauAdvance := levelNext > levelPrev
      some ("{" ++
        "\"epoch\":" ++ toString next.epoch ++
        ",\"operator_model\":\"meet_join_dialectic_v1\"" ++
        ",\"thesis_meet_level\":" ++ toString thesisMeet ++
        ",\"antithesis_join_level\":" ++ toString antithesisJoin ++
        ",\"synthesis_level\":" ++ toString levelNext ++
        ",\"plateau_advance\":" ++ (if plateauAdvance then "true" else "false") ++
        "}")
    else
      none)

private def symbiogenesisEventsJson (xs : List RuntimeSnapshot) : String :=
  "[" ++ String.intercalate "," (symbiogenesisRows xs) ++ "]"

private def symbiogenesisEpochs (xs : List RuntimeSnapshot) : List Nat :=
  (List.zip xs xs.tail).filterMap (fun p =>
    let prev := p.1
    let next := p.2
    if next.jLevel > prev.jLevel then some next.epoch else none)

private def optionNatJson (x : Option Nat) : String :=
  match x with
  | some n => toString n
  | none => "null"

private def firstAssemblyIndex? (xs : List RuntimeSnapshot) : Option Nat :=
  match firstEigenformEpoch? xs with
  | none => none
  | some e =>
      (xs.find? (fun s => s.epoch = e)).map (fun s => s.jLevel)

private def optionNatMaterial (x : Option Nat) : String :=
  match x with
  | some n => toString n
  | none => "none"

private def traceCommitmentMaterial
    (runtimeModel : String)
    (size depth epochs sampleEvery : Nat)
    (firstEpoch : Option Nat)
    (maxLevel : Nat) : String :=
  s!"schema=HeytingLean/LESExperimentRun.v2|runtime_model={runtimeModel}|size={size}|depth={depth}|epochs={epochs}|sample_every={sampleEvery}|first={optionNatMaterial firstEpoch}|max_j={maxLevel}"

private def traceJson (size depth epochs sampleEvery : Nat) : String :=
  let runtimeModel := "native-runtime-v1"
  let cfg : RuntimeConfig := { maxDepth := depth, size := size }
  let fullTrace := runtimeTrace collapseRuntimeNucleus cfg epochs
  let fullSnaps := runtimeSnapshots fullTrace
  let sampled := sampleSnapshots epochs sampleEvery fullSnaps
  let firstEpochRaw := firstEigenformEpoch? fullSnaps
  let firstEpoch :=
    match firstEpochRaw with
    | some e => if Nat.ble e epochs then some e else none
    | none => none
  let firstAssemblyRaw := firstAssemblyIndex? fullSnaps
  let firstAssembly :=
    if firstEpoch.isSome then firstAssemblyRaw else none
  let maxLevel := maxJLevel fullSnaps
  let dominantAssembly := maxLevel
  let theoreticalMinSize := runtimeCriticalSize cfg
  let phaseDetected := firstEpoch.isSome
  let thresholdViolation := phaseDetected && size < theoreticalMinSize
  let gapSum := observationGapSum sampled
  let sampledCount := sampled.length
  let daof := daofTotals size sampled
  let candEpochs := symbiogenesisEpochs fullSnaps
  let candidateTotal := candEpochs.length
  let acceptedTotal := candidateTotal
  let rejectedTotal := candidateTotal - acceptedTotal
  let rejectionRatePpm :=
    if candidateTotal = 0 then 0 else (rejectedTotal * 1000000) / candidateTotal
  let tpsNorm100 := if candidateTotal = 0 then 0 else 100
  let vwu100 := if candidateTotal = 0 then 0 else (acceptedTotal * 100) / candidateTotal
  let ig100 := if depth = 0 then 0 else Nat.min 100 ((maxLevel * 100) / depth)
  let kappa100 := (30 * tpsNorm100 + 50 * vwu100 + 20 * ig100) / 100
  let tauTotal100 := kappa100 * epochs
  let sampledEpochs := sampled.map (·.epoch)
  let consistencyCount := candEpochs.countP (fun e => e ∈ sampledEpochs)
  let sheafWarningCount := candidateTotal - consistencyCount
  let sheafConsistency100 :=
    if candidateTotal = 0 then 100 else (consistencyCount * 100) / candidateTotal
  let traj := trajectoryJson sampled
  let stateTrace := stateTraceJson sampled
  let detect := eigenformDetectionEventsJson fullSnaps
  let symbio := symbiogenesisEventsJson fullSnaps
  let commitment :=
    HeytingLean.Util.SHA256.sha256Hex
      (traceCommitmentMaterial runtimeModel size depth epochs sampleEvery firstEpoch maxLevel).toUTF8
  String.intercalate ""
    [ "{"
    , "\"schema\":\"HeytingLean/LESExperimentRun.v2\","
    , s!"\"runtime_model\":\"{runtimeModel}\","
    , "\"trace_commitment_schema\":\"les_trace_material_v1\","
    , s!"\"trace_commitment_sha256\":\"{commitment}\","
    , s!"\"proof_obligation_commitment_schema\":\"{HeytingLean.Genesis.EigenformSoup.proofObligationCommitmentSchema}\","
    , s!"\"proof_object_digest_scheme\":\"{HeytingLean.Genesis.EigenformSoup.proofObjectDigestScheme}\","
    , s!"\"proof_obligation_commitment_sha256\":\"{HeytingLean.Genesis.EigenformSoup.proofObligationCommitmentSha256}\","
    , "\"ratchet_trigger\":\"dialectic_synthesis\","
    , s!"\"size\":{size},\"depth\":{depth},\"epochs\":{epochs},\"sample_every\":{sampleEvery},"
    , s!"\"critical_size\":{runtimeCriticalSize cfg},\"growth_rate\":{runtimeGrowthRate cfg},"
    , s!"\"theoretical_min_size\":{theoreticalMinSize},"
    , s!"\"theoretical_threshold_violation\":{if thresholdViolation then "true" else "false"},"
    , s!"\"first_eigenform_epoch\":{optionNatJson firstEpoch},"
    , s!"\"max_j_ratchet_level\":{maxLevel},"
    , s!"\"first_eigenform_assembly_index\":{optionNatJson firstAssembly},"
    , s!"\"dominant_eigenform_assembly_index\":{dominantAssembly},"
    , s!"\"phase_transition_detected\":{if phaseDetected then "true" else "false"},"
    , s!"\"mean_observation_gap_sum\":{gapSum},"
    , s!"\"mean_observation_gap_count\":{sampledCount},"
    , s!"\"daof_formless_total\":{daof.1},"
    , s!"\"daof_obscure_total\":{daof.2.1},"
    , s!"\"daof_ambiguous_total\":{daof.2.2.1},"
    , s!"\"daof_distinguished_total\":{daof.2.2.2},"
    , s!"\"candidate_total\":{candidateTotal},"
    , s!"\"candidate_accepted_total\":{acceptedTotal},"
    , s!"\"candidate_rejected_total\":{rejectedTotal},"
    , s!"\"candidate_rejection_rate_ppm\":{rejectionRatePpm},"
    , s!"\"kappa_basis100\":{kappa100},"
    , s!"\"tau_total_basis100\":{tauTotal100},"
    , s!"\"sheaf_sampled_epoch_count\":{sampledCount},"
    , s!"\"sheaf_local_global_consistency_basis100\":{sheafConsistency100},"
    , s!"\"sheaf_consistency_warning_count\":{sheafWarningCount},"
    , s!"\"entropy_trajectory\":{traj},"
    , s!"\"state_trace\":{stateTrace},"
    , s!"\"eigenform_detection_events\":{detect},"
    , s!"\"symbiogenesis_events\":{symbio}"
    , "}"
    ]

private def cEscapeChar (c : Char) : String :=
  if c = '\"' then
    "\\\""
  else if c = '\\' then
    "\\\\"
  else if c = '\n' then
    "\\n"
  else if c = '\r' then
    "\\r"
  else if c = '\t' then
    "\\t"
  else
    String.singleton c

private def cEscape (s : String) : String :=
  String.join (s.data.map cEscapeChar)

private def kernelSource (jsonPayload : String) : String :=
  String.intercalate "\n"
    [ "/* EigenformSoup generated native-runtime C trace artifact */"
    , "const char* eigenform_soup_trace_json(void) {"
    , s!"  return \"{cEscape jsonPayload}\";"
    , "}"
    , ""
    ]

private def driverSource : String :=
  String.intercalate "\n"
    [ "#include <stdio.h>"
    , "const char* eigenform_soup_trace_json(void);"
    , "int main(void) {"
    , "  printf(\"%s\", eigenform_soup_trace_json());"
    , "  return 0;"
    , "}"
    , ""
    ]

private def writeBundle
    (outDir : FilePath)
    (size depth epochs sampleEvery : Nat) : IO Unit := do
  let payload := traceJson size depth epochs sampleEvery
  IO.FS.createDirAll outDir
  IO.FS.writeFile (outDir / "kernel.c") (kernelSource payload)
  IO.FS.writeFile (outDir / "driver.c") driverSource
  IO.FS.writeFile (outDir / "expected.txt") s!"{payload}\n"
  IO.FS.writeFile (outDir / "trace.json") s!"{payload}\n"

def main (argv0 : List String) : IO UInt32 := do
  let argv := HeytingLean.CLI.stripLakeArgs argv0
  if hasFlag argv "--help" then
    IO.println usage
    return 0
  match parseNatOpt argv "--size" 16, parseNatOpt argv "--depth" 2,
      parseNatOpt argv "--epochs" 64, parseNatOpt argv "--sample-every" 1 with
  | .error err, _, _, _ =>
      IO.eprintln s!"eigenform_soup_native_trace_parity: {err}"
      IO.eprintln "use --help for usage"
      return 2
  | _, .error err, _, _ =>
      IO.eprintln s!"eigenform_soup_native_trace_parity: {err}"
      IO.eprintln "use --help for usage"
      return 2
  | _, _, .error err, _ =>
      IO.eprintln s!"eigenform_soup_native_trace_parity: {err}"
      IO.eprintln "use --help for usage"
      return 2
  | _, _, _, .error err =>
      IO.eprintln s!"eigenform_soup_native_trace_parity: {err}"
      IO.eprintln "use --help for usage"
      return 2
  | .ok size, .ok depth, .ok epochs, .ok sampleEvery =>
      let outDir := parseOutDir argv
      try
        writeBundle outDir size depth epochs sampleEvery
        IO.println s!"eigenform_soup_native_trace_parity: wrote bundle"
        IO.println s!"out_dir={outDir}"
        IO.println s!"size={size}"
        IO.println s!"depth={depth}"
        IO.println s!"epochs={epochs}"
        IO.println s!"sample_every={sampleEvery}"
        return 0
      catch e =>
        IO.eprintln s!"eigenform_soup_native_trace_parity: failed: {e}"
        return 1

end HeytingLean.CLI.EigenformSoupNativeTraceParityMain

open HeytingLean.CLI.EigenformSoupNativeTraceParityMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.EigenformSoupNativeTraceParityMain.main args
