import HeytingLean.Genesis.EigenformSoup.Extraction
import HeytingLean.Genesis.EigenformSoup.NoncomputableBridge
import HeytingLean.Genesis.EigenformSoup.PhaseGates

/-!
# Genesis.EigenformSoup.Main

WS9 deterministic reporting entrypoint for EigenformSoup.
-/

namespace HeytingLean.Genesis.EigenformSoup

/-- CLI-facing deterministic run options for the initial milestone. -/
structure CliConfig where
  depth : Nat := 4
  size : Nat := 16
  fuel : Nat := 16
deriving Repr

/-- Convert CLI options into runner configuration. -/
def toSoupConfig (cfg : CliConfig) : SoupConfig :=
  { substrate := { maxDepth := cfg.depth, size := cfg.size }
    fuel := cfg.fuel }

/-- Deterministic textual report from one soup run. -/
noncomputable def runDeterministicReport
    (nuc : SoupNucleus)
    (cfg : CliConfig) : String :=
  let soupCfg := toSoupConfig cfg
  let certified := certifyRun nuc soupCfg
  let cab := mkCertifiedSoupCAB nuc soupCfg
  let compiled := compileSoupCAB nuc soupCfg
  let trace := runSoupTrace nuc soupCfg
  let traceSnapshots := runSoupTraceSnapshots nuc soupCfg
  let dialecticEvents := scheduledEvents certified.finalState
  let synthesisSupports := stabilizedSupports nuc dialecticEvents
  let proofHashHex := HeytingLean.Util.SHA256.toHex cab.proofCommitment.hash
  let proofObligationHash := proofObligationCommitmentSha256
  s!"EigenformSoup report\n\
      substrate_size={soupCfg.substrate.size}\n\
      epoch={certified.stats.steps}\n\
      trace_points={trace.length}\n\
      trace_snapshot_points={traceSnapshots.length}\n\
      trace_snapshot_checksum={traceSnapshotChecksum traceSnapshots}\n\
      stabilized={certified.stats.stabilizedCount}\n\
      proof_hash_sha256={proofHashHex}\n\
      proof_obligation_commitment_sha256={proofObligationHash}\n\
      metadata_timestamp={cab.metadata.timestamp}\n\
      ratchet_trigger=dialectic_synthesis\n\
      dialectic_events={dialecticEvents.length}\n\
      synthesis_candidates={synthesisSupports.length}\n\
      c_artifact_bytes={compiled.cCode.length}\n\
      allStagesCorrect={compiled.allStagesCorrect}"

/-- Runtime WS9 gate inputs supplied from external checks. -/
structure GateInputs where
  boundaryOk : Bool
  r3Ok : Bool
deriving Repr

/-- Boolean WS9 gate status for CLI/reporting use. -/
noncomputable def ws9GateStatus
    (nuc : SoupNucleus)
    (cfg : CliConfig)
    (inputs : GateInputs) : Bool :=
  let soupCfg := toSoupConfig cfg
  let compiled := compileSoupCAB nuc soupCfg
  let expectedC := renderC ((runSoup nuc soupCfg).stabilized.length)
  inputs.boundaryOk && inputs.r3Ok &&
    compiled.allStagesCorrect &&
    (compiled.cCode == expectedC)

theorem ws9GateStatus_true_of_all_true
    (nuc : SoupNucleus)
    (cfg : CliConfig) :
    ws9GateStatus nuc cfg { boundaryOk := true, r3Ok := true } = true := by
  have hCCode :
      (compileSoupCAB nuc (toSoupConfig cfg)).cCode =
        renderC ((runSoup nuc (toSoupConfig cfg)).stabilized.length) := by
    simpa [CHasStabilizedCount] using
      (compileSoupCAB_cCode_has_stabilizedCount nuc (toSoupConfig cfg))
  simp [ws9GateStatus, compileSoupCAB_allStagesCorrect, hCCode]

theorem ws9GateStatus_false_if_r3_false
    (nuc : SoupNucleus)
    (cfg : CliConfig) :
    ws9GateStatus nuc cfg { boundaryOk := true, r3Ok := false } = false := by
  simp [ws9GateStatus]

theorem runDeterministicReport_deterministic
    (nuc : SoupNucleus)
    (cfg : CliConfig) :
    runDeterministicReport nuc cfg = runDeterministicReport nuc cfg := rfl

/-- Default milestone report using the WS1 collapse-policy nucleus. -/
noncomputable def defaultReport : String :=
  runDeterministicReport collapsePolicy {}

end HeytingLean.Genesis.EigenformSoup
