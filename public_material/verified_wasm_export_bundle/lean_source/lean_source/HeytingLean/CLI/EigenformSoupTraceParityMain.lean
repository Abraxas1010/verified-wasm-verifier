import HeytingLean.CLI.Args
import HeytingLean.Genesis.EigenformSoup.NoncomputableBridge
import HeytingLean.Util.SHA

/-!
# EigenformSoup trace parity bundle generator

Emits a C bundle for runtime parity checks over a deterministic LES trace payload:
- `kernel.c`        : generated C function returning one JSON trace line
- `driver.c`        : calls `eigenform_soup_trace_json()`
- `expected.txt`    : expected JSON line output
- `trace.json`      : same JSON payload (for sweep scripts)

This executable is an experiment-protocol scaffold for size/depth sweeps while the
full theorem-oriented `runSoup` runtime remains noncomputable.
-/

namespace HeytingLean.CLI.EigenformSoupTraceParityMain

open System

private def usage : String :=
  String.intercalate "\n"
    [ "eigenform_soup_trace_parity"
    , "  Generates a runtime parity C bundle for LES trace payloads."
    , ""
    , "Options:"
    , "  --size <nat> | --size=<nat>            substrate size (default: 16)"
    , "  --depth <nat> | --depth=<nat>          substrate depth (default: 2)"
    , "  --epochs <nat> | --epochs=<nat>        max epochs (default: 64)"
    , "  --sample-every <nat> | --sample-every=<nat>  sample interval (default: 1)"
    , "  --out-dir <path> | --out-dir=<path>    output directory (default: dist/eigenform_soup_trace_parity)"
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
  let raw := (findOptValue argv "--out-dir").getD "dist/eigenform_soup_trace_parity"
  FilePath.mk raw

private def criticalSize (depth : Nat) : Nat :=
  Nat.shiftLeft 1 (depth + 2)

private def growthRate (size depth : Nat) : Nat :=
  if size < criticalSize depth then 0 else size - criticalSize depth + 1

private def firstEigenformEpoch? (size depth : Nat) : Option Nat :=
  let rate := growthRate size depth
  if rate = 0 then none else some (Nat.max 1 (criticalSize depth / rate))

private def stabilizedAt (size depth epoch : Nat) : Nat :=
  let rate := growthRate size depth
  match firstEigenformEpoch? size depth with
  | none => 0
  | some first =>
      if epoch < first then 0 else (epoch - first + 1) * rate

private def entropyAt (size depth epoch : Nat) : Nat :=
  size - stabilizedAt size depth epoch

private def jLevelAt (size depth epoch : Nat) : Nat :=
  stabilizedAt size depth epoch

private def sampleEpochs (epochs sampleEvery : Nat) : List Nat :=
  let step := if sampleEvery = 0 then 1 else sampleEvery
  (List.range (epochs + 1)).filter (fun e => e % step = 0 || e = epochs)

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

private def daofTotals (size depth epochs sampleEvery : Nat) : Nat × Nat × Nat × Nat :=
  let near := nearThreshold size
  (sampleEpochs epochs sampleEvery).foldl
    (fun acc e => addCounts acc (daofCountsAt size (entropyAt size depth e) near))
    (0, 0, 0, 0)

private def observationGapSum (size depth epochs sampleEvery : Nat) : Nat :=
  (sampleEpochs epochs sampleEvery).foldl (fun acc e => acc + entropyAt size depth e) 0

private def candidateEpochs (size depth epochs : Nat) : List Nat :=
  if growthRate size depth = 0 then
    []
  else
    let first := (firstEigenformEpoch? size depth).getD (epochs + 1)
    (List.range epochs).filter (fun e => first ≤ e + 1) |>.map (· + 1)

private def trajectoryEntryJson (size depth epoch : Nat) : String :=
  "{" ++
    "\"epoch\":" ++ toString epoch ++
    ",\"entropy\":" ++ toString (entropyAt size depth epoch) ++
    ",\"stabilized\":" ++ toString (stabilizedAt size depth epoch) ++
    ",\"j_level\":" ++ toString (jLevelAt size depth epoch) ++
    "}"

private def trajectoryJson (size depth epochs sampleEvery : Nat) : String :=
  let xs := (sampleEpochs epochs sampleEvery).map (trajectoryEntryJson size depth)
  "[" ++ String.intercalate "," xs ++ "]"

private def stateTraceEntryJson (size depth epoch : Nat) : String :=
  "{" ++
    "\"epoch\":" ++ toString epoch ++
    ",\"stabilized_count\":" ++ toString (stabilizedAt size depth epoch) ++
    ",\"entropy\":" ++ toString (entropyAt size depth epoch) ++
    ",\"j_level\":" ++ toString (jLevelAt size depth epoch) ++
    "}"

private def stateTraceJson (size depth epochs sampleEvery : Nat) : String :=
  let xs := (sampleEpochs epochs sampleEvery).map (stateTraceEntryJson size depth)
  "[" ++ String.intercalate "," xs ++ "]"

private def symbiogenesisEventsJson (size depth epochs : Nat) : String :=
  let xs :=
    (candidateEpochs size depth epochs).map (fun epoch =>
      let e := epoch - 1
        let levelPrev := jLevelAt size depth e
        let levelNext := jLevelAt size depth epoch
        let thesisMeet := levelPrev / 2
        let antithesisJoin := levelPrev - thesisMeet + growthRate size depth
        let plateauAdvance := levelNext > levelPrev
        "{" ++
          "\"epoch\":" ++ toString epoch ++
          ",\"operator_model\":\"meet_join_dialectic_v1\"" ++
          ",\"thesis_meet_level\":" ++ toString thesisMeet ++
          ",\"antithesis_join_level\":" ++ toString antithesisJoin ++
          ",\"synthesis_level\":" ++ toString levelNext ++
          ",\"plateau_advance\":" ++ (if plateauAdvance then "true" else "false") ++
          "}")
  "[" ++ String.intercalate "," xs ++ "]"

private def eigenformDetectionEventsJson (size depth epochs : Nat) : String :=
  let first := (firstEigenformEpoch? size depth).getD (epochs + 1)
  let xs :=
    (candidateEpochs size depth epochs).map (fun epoch =>
        let eventTag := if epoch = first then "first_eigenform" else "plateau_synthesis"
        "{" ++
          "\"epoch\":" ++ toString epoch ++
          ",\"event\":\"" ++ eventTag ++ "\"" ++
          ",\"assembly_index\":" ++ toString (jLevelAt size depth epoch) ++
          "}")
  "[" ++ String.intercalate "," xs ++ "]"

private def optionNatJson (x : Option Nat) : String :=
  match x with
  | some n => toString n
  | none => "null"

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
  let runtimeModel := "invariant-proxy-v1"
  let firstEpochRaw := firstEigenformEpoch? size depth
  let firstEpoch :=
    match firstEpochRaw with
    | some e => if Nat.ble e epochs then some e else none
    | none => none
  let maxLevel := jLevelAt size depth epochs
  let dominantAssembly := if maxLevel = 0 then 0 else maxLevel
  let theoreticalMinSize := criticalSize depth
  let phaseDetected := firstEpoch.isSome
  let thresholdViolation := phaseDetected && size < theoreticalMinSize
  let sampledEpochs := sampleEpochs epochs sampleEvery
  let sampledCount := sampledEpochs.length
  let gapSum := observationGapSum size depth epochs sampleEvery
  let daof := daofTotals size depth epochs sampleEvery
  let candEpochs := candidateEpochs size depth epochs
  let candidateTotal := candEpochs.length
  let acceptedTotal := candidateTotal
  let rejectedTotal := candidateTotal - acceptedTotal
  let rejectionRatePpm :=
    if candidateTotal = 0 then 0 else (rejectedTotal * 1000000) / candidateTotal
  let tpsNorm100 := if candidateTotal = 0 then 0 else 100
  let vwu100 := if candidateTotal = 0 then 0 else (acceptedTotal * 100) / candidateTotal
  let ig100 :=
    if depth = 0 then 0 else Nat.min 100 ((maxLevel * 100) / depth)
  let kappa100 := (30 * tpsNorm100 + 50 * vwu100 + 20 * ig100) / 100
  let tauTotal100 := kappa100 * epochs
  let sampledEpochCount := sampledEpochs.length
  let consistencyCount :=
    candEpochs.countP (fun e => e ∈ sampledEpochs)
  let sheafWarningCount := candidateTotal - consistencyCount
  let sheafConsistency100 :=
    if candidateTotal = 0 then 100 else (consistencyCount * 100) / candidateTotal
  let symbio := symbiogenesisEventsJson size depth epochs
  let traj := trajectoryJson size depth epochs sampleEvery
  let stateTrace := stateTraceJson size depth epochs sampleEvery
  let detect := eigenformDetectionEventsJson size depth epochs
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
    , s!"\"critical_size\":{criticalSize depth},\"growth_rate\":{growthRate size depth},"
    , s!"\"theoretical_min_size\":{theoreticalMinSize},"
    , s!"\"theoretical_threshold_violation\":{if thresholdViolation then "true" else "false"},"
    , s!"\"first_eigenform_epoch\":{optionNatJson firstEpoch},"
    , s!"\"max_j_ratchet_level\":{maxLevel},"
    , s!"\"first_eigenform_assembly_index\":{optionNatJson firstEpoch},"
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
    , s!"\"sheaf_sampled_epoch_count\":{sampledEpochCount},"
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
    [ "/* EigenformSoup generated C trace artifact (protocol scaffold) */"
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
    (outDir : FilePath) (size depth epochs sampleEvery : Nat) : IO Unit := do
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
      IO.eprintln s!"eigenform_soup_trace_parity: {err}"
      IO.eprintln "use --help for usage"
      return 2
  | _, .error err, _, _ =>
      IO.eprintln s!"eigenform_soup_trace_parity: {err}"
      IO.eprintln "use --help for usage"
      return 2
  | _, _, .error err, _ =>
      IO.eprintln s!"eigenform_soup_trace_parity: {err}"
      IO.eprintln "use --help for usage"
      return 2
  | _, _, _, .error err =>
      IO.eprintln s!"eigenform_soup_trace_parity: {err}"
      IO.eprintln "use --help for usage"
      return 2
  | .ok size, .ok depth, .ok epochs, .ok sampleEvery =>
      let outDir := parseOutDir argv
      try
        writeBundle outDir size depth epochs sampleEvery
        IO.println s!"eigenform_soup_trace_parity: wrote bundle"
        IO.println s!"out_dir={outDir}"
        IO.println s!"size={size}"
        IO.println s!"depth={depth}"
        IO.println s!"epochs={epochs}"
        IO.println s!"sample_every={sampleEvery}"
        return 0
      catch e =>
        IO.eprintln s!"eigenform_soup_trace_parity: failed: {e}"
        return 1

end HeytingLean.CLI.EigenformSoupTraceParityMain

open HeytingLean.CLI.EigenformSoupTraceParityMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.EigenformSoupTraceParityMain.main args
