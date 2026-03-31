import HeytingLean.Genesis.EigenformSoup.Runner
import HeytingLean.Genesis.EigenformSoup.BridgeCommitment
import HeytingLean.CAB.Compile

/-!
# Genesis.EigenformSoup.Extraction

WS8 extraction scaffolding for deterministic soup runs.
Milestone target: C artifact generation + compile proof-of-build.
-/

namespace HeytingLean.Genesis.EigenformSoup

open HeytingLean

/-- Soup specification used for CAB packaging. -/
def SoupSpec (nuc : SoupNucleus) (s : SoupState nuc) : Prop :=
  ∀ S, S ∈ s.stabilized → isEigenform nuc S

/-- Extract a nat literal payload from a typed LambdaIR term when possible. -/
def lambdaIRNatLiteral? (ir : LambdaIR.TypedTerm) : Option Nat :=
  match ir.Γ, ir.τ, ir.term with
  | [], HeytingLean.Core.Ty.nat, LambdaIR.Term.constNat n => some n
  | _, _, _ => none

/-- Deterministic MiniC renderer for the stabilized-count payload. -/
def renderMiniC (n : Nat) : String :=
  "int eigenform_soup_stabilized_count(void) { return " ++ toString n ++ "; }\n"

/-- Deterministic MiniC renderer for the trace-checksum payload. -/
def renderTraceChecksumMiniC (n : Nat) : String :=
  "int eigenform_soup_trace_checksum(void) { return " ++ toString n ++ "; }\n"

/-- Header used for generated soup C artifacts. -/
def cArtifactHeader : String :=
  "/* EigenformSoup generated C artifact (milestone-1 scaffold) */\n"

/-- Deterministic C renderer for the stabilized-count payload. -/
def renderC (n : Nat) : String :=
  cArtifactHeader ++ renderMiniC n

/-- Deterministic C renderer for the trace-checksum payload. -/
def renderTraceChecksumC (n : Nat) : String :=
  cArtifactHeader ++ renderTraceChecksumMiniC n

/-- Stage-1 adapter: soup artifact to a typed LambdaIR term. -/
def soupToLambdaIR {nuc : SoupNucleus} (s : SoupState nuc) : LambdaIR.TypedTerm :=
  { Γ := []
    τ := HeytingLean.Core.Ty.nat
    term := LambdaIR.Term.constNat s.stabilized.length }

/-- Stage-2 adapter: LambdaIR term to MiniC text placeholder. -/
def lambdaIRToMiniC (ir : LambdaIR.TypedTerm) : String :=
  renderMiniC ((lambdaIRNatLiteral? ir).getD 0)

/-- Stage-3 adapter: MiniC text to C artifact text. -/
def miniCToC (miniC : String) : String :=
  cArtifactHeader ++ miniC

/-- Semantic relation: MiniC text carries a specific stabilized-count payload. -/
def MiniCHasStabilizedCount (mini : String) (n : Nat) : Prop :=
  mini = renderMiniC n

/-- Semantic relation: C artifact carries a specific stabilized-count payload. -/
def CHasStabilizedCount (c : String) (n : Nat) : Prop :=
  c = renderC n

/-- Stage relation: soup artifact maps to the chosen LambdaIR term. -/
def SoupToLambdaIRRel {nuc : SoupNucleus} (s : SoupState nuc) (ir : LambdaIR.TypedTerm) : Prop :=
  ir = soupToLambdaIR s ∧ lambdaIRNatLiteral? ir = some s.stabilized.length

/-- Stage relation: LambdaIR term maps to generated MiniC text. -/
def LambdaIRToMiniCRel (ir : LambdaIR.TypedTerm) (mini : String) : Prop :=
  mini = lambdaIRToMiniC ir ∧
    match lambdaIRNatLiteral? ir with
    | some n => MiniCHasStabilizedCount mini n
    | none => MiniCHasStabilizedCount mini 0

/-- Stage relation: MiniC text maps to generated C artifact text. -/
def MiniCToCRel (mini c : String) : Prop :=
  c = miniCToC mini ∧
    ∀ n, MiniCHasStabilizedCount mini n → CHasStabilizedCount c n

/-- Deterministic config fingerprint used for CAB metadata timestamps. -/
def soupConfigFingerprint (cfg : SoupConfig) : Nat :=
  cfg.substrate.size * 1000000 + cfg.substrate.maxDepth * 1000 + cfg.fuel

/-- Deterministic proof-material payload for stabilized-count CAB commitments. -/
def soupProofMaterial (cfg : SoupConfig) (stabilizedCount : Nat) : String :=
  s!"EigenformSoup/stabilized|size={cfg.substrate.size}|depth={cfg.substrate.maxDepth}|fuel={cfg.fuel}|stabilized={stabilizedCount}|proof_obligation_commitment_sha256={proofObligationCommitmentSha256}|proof_object_digest_scheme={proofObjectDigestScheme}"

/-- Stabilized-count proof material explicitly includes bridge commitment anchors. -/
theorem soupProofMaterial_bridgeAnchored (cfg : SoupConfig) (stabilizedCount : Nat) :
    soupProofMaterial cfg stabilizedCount =
      s!"EigenformSoup/stabilized|size={cfg.substrate.size}|depth={cfg.substrate.maxDepth}|fuel={cfg.fuel}|stabilized={stabilizedCount}|proof_obligation_commitment_sha256={proofObligationCommitmentSha256}|proof_object_digest_scheme={proofObjectDigestScheme}" :=
  rfl

/-- Deterministic SHA-256 commitment for a proof-material payload. -/
def proofHashOfMaterial (material : String) : CAB.ProofHash :=
  { hash := HeytingLean.Util.SHA256.sha256Bytes material.toUTF8
    algorithm := "SHA256" }

/-- Deterministic stabilized-count CAB commitment. -/
def soupProofHash {nuc : SoupNucleus} (cfg : SoupConfig) (s : SoupState nuc) : CAB.ProofHash :=
  proofHashOfMaterial (soupProofMaterial cfg s.stabilized.length)

/-- Deterministic CAB metadata for soup extraction. -/
def soupMetadata (cfg : SoupConfig) : CAB.CABMetadata :=
  { fragment := .Custom "EigenformSoup"
    dimension := .D1
    lensCompatibility := [.Topology, .Graph]
    timestamp := soupConfigFingerprint cfg }

/-- Build a CAB around a deterministic soup run. -/
noncomputable def mkCertifiedSoupCAB (nuc : SoupNucleus) (cfg : SoupConfig) :
    HeytingLean.CAB (SoupState nuc) (SoupSpec nuc) :=
  let finalState := runSoup nuc cfg
  { artifact := finalState
    spec := by
      intro S hS
      exact runSoup_sound nuc cfg S hS
    proofCommitment := soupProofHash cfg finalState
    metadata := soupMetadata cfg }

/-- Artifact carrying final state plus a trace-derived checksum payload. -/
structure SoupTraceArtifact (nuc : SoupNucleus) where
  finalState : SoupState nuc
  traceChecksum : Nat

/-- Trace artifact spec mirrors soup soundness on the final state. -/
def SoupTraceSpec (nuc : SoupNucleus) (a : SoupTraceArtifact nuc) : Prop :=
  ∀ S, S ∈ a.finalState.stabilized → isEigenform nuc S

/-- Deterministic proof-material payload for trace-checksum CAB commitments. -/
def soupTraceProofMaterial {nuc : SoupNucleus} (cfg : SoupConfig) (a : SoupTraceArtifact nuc) : String :=
  s!"EigenformSoup/trace|size={cfg.substrate.size}|depth={cfg.substrate.maxDepth}|fuel={cfg.fuel}|stabilized={a.finalState.stabilized.length}|trace_checksum={a.traceChecksum}|proof_obligation_commitment_sha256={proofObligationCommitmentSha256}|proof_object_digest_scheme={proofObjectDigestScheme}"

/-- Trace proof material explicitly includes bridge commitment anchors. -/
theorem soupTraceProofMaterial_bridgeAnchored
    {nuc : SoupNucleus} (cfg : SoupConfig) (a : SoupTraceArtifact nuc) :
    soupTraceProofMaterial cfg a =
      s!"EigenformSoup/trace|size={cfg.substrate.size}|depth={cfg.substrate.maxDepth}|fuel={cfg.fuel}|stabilized={a.finalState.stabilized.length}|trace_checksum={a.traceChecksum}|proof_obligation_commitment_sha256={proofObligationCommitmentSha256}|proof_object_digest_scheme={proofObjectDigestScheme}" :=
  rfl

/-- Deterministic trace-checksum CAB commitment. -/
def soupTraceProofHash {nuc : SoupNucleus}
    (cfg : SoupConfig) (a : SoupTraceArtifact nuc) : CAB.ProofHash :=
  proofHashOfMaterial (soupTraceProofMaterial cfg a)

/-- Build a deterministic trace artifact from trace snapshots. -/
noncomputable def mkSoupTraceArtifact (nuc : SoupNucleus) (cfg : SoupConfig) :
    SoupTraceArtifact nuc :=
  { finalState := runSoup nuc cfg
    traceChecksum := traceSnapshotChecksum (runSoupTraceSnapshots nuc cfg) }

/-- Build a CAB around the deterministic trace artifact. -/
noncomputable def mkCertifiedSoupTraceCAB (nuc : SoupNucleus) (cfg : SoupConfig) :
    HeytingLean.CAB (SoupTraceArtifact nuc) (SoupTraceSpec nuc) :=
  let artifact := mkSoupTraceArtifact nuc cfg
  { artifact := artifact
    spec := by
      intro S hS
      exact runSoup_sound nuc cfg S hS
    proofCommitment := soupTraceProofHash cfg artifact
    metadata := soupMetadata cfg }

/-- Stage-1 adapter for trace artifact payloads. -/
def soupTraceToLambdaIR {nuc : SoupNucleus} (a : SoupTraceArtifact nuc) : LambdaIR.TypedTerm :=
  { Γ := []
    τ := HeytingLean.Core.Ty.nat
    term := LambdaIR.Term.constNat a.traceChecksum }

/-- Stage-2 adapter for trace artifact payloads. -/
def soupTraceLambdaIRToMiniC (ir : LambdaIR.TypedTerm) : String :=
  renderTraceChecksumMiniC ((lambdaIRNatLiteral? ir).getD 0)

/-- Stage-3 adapter for trace artifact payloads. -/
def soupTraceMiniCToC (miniC : String) : String :=
  cArtifactHeader ++ miniC

/-- Compile deterministic soup CAB through LambdaIR -> MiniC -> C adapters. -/
noncomputable def compileSoupCAB (nuc : SoupNucleus) (cfg : SoupConfig) : CAB.CompilationResult :=
  CAB.compileCAB
    (cab := mkCertifiedSoupCAB nuc cfg)
    (toLambdaIR := soupToLambdaIR)
    (toMiniC := lambdaIRToMiniC)
    (toC := miniCToC)

/-- Compile deterministic trace CAB through LambdaIR -> MiniC -> C adapters. -/
noncomputable def compileSoupTraceCAB (nuc : SoupNucleus) (cfg : SoupConfig) : CAB.CompilationResult :=
  CAB.compileCAB
    (cab := mkCertifiedSoupTraceCAB nuc cfg)
    (toLambdaIR := soupTraceToLambdaIR)
    (toMiniC := soupTraceLambdaIRToMiniC)
    (toC := soupTraceMiniCToC)

theorem soupToLambdaIR_literal
    {nuc : SoupNucleus}
    (s : SoupState nuc) :
    lambdaIRNatLiteral? (soupToLambdaIR s) = some s.stabilized.length :=
  rfl

theorem soupToLambdaIRRel_of_adapter
    {nuc : SoupNucleus}
    (s : SoupState nuc) :
    SoupToLambdaIRRel s (soupToLambdaIR s) :=
  ⟨rfl, soupToLambdaIR_literal s⟩

theorem lambdaIRToMiniCRel_of_adapter
    (ir : LambdaIR.TypedTerm) :
    LambdaIRToMiniCRel ir (lambdaIRToMiniC ir) := by
  cases hLit : lambdaIRNatLiteral? ir <;>
    simp [LambdaIRToMiniCRel, lambdaIRToMiniC, MiniCHasStabilizedCount, hLit]

theorem miniCToCRel_of_adapter
    (mini : String) :
    MiniCToCRel mini (miniCToC mini) := by
  refine ⟨rfl, ?_⟩
  intro n hMini
  rcases hMini with rfl
  rfl

theorem compileSoupCAB_stage_relations
    (nuc : SoupNucleus)
    (cfg : SoupConfig) :
    let cab := mkCertifiedSoupCAB nuc cfg
    let out := compileSoupCAB nuc cfg
    SoupToLambdaIRRel cab.artifact out.lambdaIR ∧
      LambdaIRToMiniCRel out.lambdaIR out.miniC ∧
      MiniCToCRel out.miniC out.cCode := by
  simp [compileSoupCAB, CAB.compileCAB, soupToLambdaIRRel_of_adapter, lambdaIRToMiniCRel_of_adapter,
    miniCToCRel_of_adapter]

theorem compileSoupCAB_cCode_has_stabilizedCount
    (nuc : SoupNucleus)
    (cfg : SoupConfig) :
    CHasStabilizedCount
      (compileSoupCAB nuc cfg).cCode
      ((runSoup nuc cfg).stabilized.length) := by
  simp [CHasStabilizedCount, renderC, compileSoupCAB, CAB.compileCAB, mkCertifiedSoupCAB,
    miniCToC, lambdaIRToMiniC, soupToLambdaIR, lambdaIRNatLiteral?, renderMiniC]

theorem compileSoupCAB_allStagesCorrect (nuc : SoupNucleus) (cfg : SoupConfig) :
    (compileSoupCAB nuc cfg).allStagesCorrect = true := rfl

theorem compileSoupTraceCAB_cCode_has_traceChecksum
    (nuc : SoupNucleus)
    (cfg : SoupConfig) :
    (compileSoupTraceCAB nuc cfg).cCode =
      renderTraceChecksumC ((mkSoupTraceArtifact nuc cfg).traceChecksum) := by
  simp [compileSoupTraceCAB, CAB.compileCAB, mkCertifiedSoupTraceCAB, mkSoupTraceArtifact,
    soupTraceMiniCToC, soupTraceLambdaIRToMiniC, soupTraceToLambdaIR, lambdaIRNatLiteral?,
    renderTraceChecksumC, renderTraceChecksumMiniC]

theorem compileSoupTraceCAB_allStagesCorrect (nuc : SoupNucleus) (cfg : SoupConfig) :
    (compileSoupTraceCAB nuc cfg).allStagesCorrect = true := rfl

theorem mkCertifiedSoupCAB_commitment_eq
    (nuc : SoupNucleus) (cfg : SoupConfig) :
    (mkCertifiedSoupCAB nuc cfg).proofCommitment =
      soupProofHash cfg (runSoup nuc cfg) := by
  simp [mkCertifiedSoupCAB]

theorem mkCertifiedSoupTraceCAB_commitment_eq
    (nuc : SoupNucleus) (cfg : SoupConfig) :
    (mkCertifiedSoupTraceCAB nuc cfg).proofCommitment =
      soupTraceProofHash cfg (mkSoupTraceArtifact nuc cfg) := by
  simp [mkCertifiedSoupTraceCAB]

end HeytingLean.Genesis.EigenformSoup
