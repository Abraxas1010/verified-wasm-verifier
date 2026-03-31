import HeytingLean.Crypto.KEM.MLKEM203Params
import HeytingLean.Crypto.KEM.MLKEMPKECompressed
import HeytingLean.Crypto.KEM.MLKEMFailureConservative
import HeytingLean.Crypto.KEM.MLKEMProofLine
import HeytingLean.Crypto.Lattice.RecoveryViews
import HeytingLean.Crypto.Security.Advantage
import HeytingLean.Crypto.Security.Reduction

namespace HeytingLean
namespace Crypto
namespace KEM

/-!
# ML-KEM security statement shells (proof-line upgrade)

This file records the repository-native ML-KEM security surface after removing the old
`Prop := True` placeholder.

The current object is a theorem-shape bundle that points to the imported EasyCrypt / FO proof
line and the published FIPS 203 failure bound. It is still a bridge surface rather than a
full Lean-native IND-CCA proof.
-/

namespace Security

open HeytingLean.Crypto.Lattice
open FIPS203

/-- Repository-native IND-CCA statement bundle for a FIPS 203 parameter set. -/
abbrev IND_CCA (p : FIPS203.MLKEM203Params) : Type :=
  FIPS203.ProofLine.StatementBundle p

/-- Statement shape for deriving the IND-CCA claim under an MLWE hardness assumption. -/
structure IND_CCA_under_MLWE (p : FIPS203.MLKEM203Params) (P : MLWEParams) where
  derive : Unsolvable (MLWEView P) → IND_CCA p

/-- Explicit witness for the shared-game MLWE assumption input. -/
structure MLWEAssumptionWitness (p : FIPS203.MLKEM203Params) where
  token : Unit := ()
  witness : Unsolvable (MLWEView (FIPS203.toMLWEParams p))

/-- Shared-game target for the current native ML-KEM security surface. -/
noncomputable def nativeINDCCAGame (p : FIPS203.MLKEM203Params) : HeytingLean.Crypto.Security.Game where
  State := Unit
  Transcript := FIPS203.MLKEM203Params × MLWEParams
  Challenge := FIPS203.MLKEM203Params
  Output := IND_CCA p
  init := ()
  transcript := fun _ => (p, FIPS203.toMLWEParams p)
  challenge := fun _ => p
  output := fun _ => ProofLine.importedEpisodeV p

/-- Shared-oracle budget induced from the imported FO reduction shell. -/
noncomputable def nativeINDCCAOracle : FIPS203.MLKEM203Params → HeytingLean.Crypto.Security.OracleModel ByteArray ByteArray
  | p =>
      { budget :=
          { randomOracleQueries := (ProofLine.importedEpisodeV p).foReduction.budget.randomOracleQueries
            decapsulationQueries := (ProofLine.importedEpisodeV p).foReduction.budget.decapsulationQueries
            signingQueries := 0
            auxiliaryQueries := 0 }
        answer := some }

/-- Shared advantage surface for the current imported-shell target. -/
def nativeINDCCAAdvantage (_p : FIPS203.MLKEM203Params) : HeytingLean.Crypto.Security.Advantage :=
  { challenge0 := 0, challenge1 := 0 }

/-- Shared reduction target for the current ML-KEM security shell. -/
noncomputable def nativeINDCCAReduction (p : FIPS203.MLKEM203Params) :
    HeytingLean.Crypto.Security.Reduction
      (MLWEAssumptionWitness p)
      (IND_CCA p) where
  budget := (nativeINDCCAOracle p).budget
  transform := fun _ => ProofLine.importedEpisodeV p
  lossUpperBound := 0

theorem nativeINDCCAGame_output (p : FIPS203.MLKEM203Params) :
    (nativeINDCCAGame p).output (nativeINDCCAGame p).init = ProofLine.importedEpisodeV p := rfl

theorem nativeINDCCAOracle_matches_imported_budget (p : FIPS203.MLKEM203Params) :
    (nativeINDCCAOracle p).budget.randomOracleQueries =
        (ProofLine.importedEpisodeV p).foReduction.budget.randomOracleQueries ∧
      (nativeINDCCAOracle p).budget.decapsulationQueries =
        (ProofLine.importedEpisodeV p).foReduction.budget.decapsulationQueries := by
  exact ⟨rfl, rfl⟩

theorem importedINDCCA_uses_local_compressed_correctness
    (p : FIPS203.MLKEM203Params)
    (codec : KPKE.MsgCodec p) (pk : KPKE.PublicKey p)
    (sk : KPKE.SecretKey p) (e : KPKE.ModVec p)
    (ht : pk.t = pk.A.mulVec sk.s + e)
    (m : codec.Msg) (r e1 : KPKE.ModVec p) (e2 : KPKE.Rq p)
    (hgood :
      codec.good
        (KPKE.dot e r + e2 - KPKE.dot sk.s e1
          + KPKECompressed.compressionNoise (p := p) sk (KPKE.encryptDet codec pk m r e1 e2))) :
    let bundle : IND_CCA p := ProofLine.importedEpisodeV p
    bundle.mlweParams = FIPS203.toMLWEParams p ∧
      KPKECompressed.decryptCompressed (p := p) codec sk
        (KPKECompressed.encryptCompressed (p := p) codec pk m r e1 e2) = m := by
  exact ⟨rfl, KPKECompressed.decrypt_encryptCompressed codec pk sk e ht m r e1 e2 hgood⟩

theorem importedINDCCA_mlkem512_uses_local_failure_proxy :
    let bundle : IND_CCA FIPS203.mlkem512 := ProofLine.importedEpisodeV FIPS203.mlkem512
    bundle.decryptionFailure.bound.numericUpperBound = some (reportedFailureBoundQ FIPS203.mlkem512) ∧
      ConservativeBounds.failureProbabilityComputed FIPS203.mlkem512
        (FIPS203.mlkem512.k * FIPS203.mlkem512.n)
        (ConservativeBounds.adjustedThreshold ConservativeBounds.Acomp512) <
          reportedFailureBoundQ FIPS203.mlkem512 := by
  exact ⟨rfl, ConservativeBounds.mlkem512_failureProbabilityComputed_with_compression_lt_reportedFailureBoundQ⟩

theorem importedINDCCA_mlkem768_uses_local_failure_proxy :
    let bundle : IND_CCA FIPS203.mlkem768 := ProofLine.importedEpisodeV FIPS203.mlkem768
    bundle.decryptionFailure.bound.numericUpperBound = some (reportedFailureBoundQ FIPS203.mlkem768) ∧
      ConservativeBounds.failureProbabilityComputed FIPS203.mlkem768
        (FIPS203.mlkem768.k * FIPS203.mlkem768.n)
        (ConservativeBounds.adjustedThreshold ConservativeBounds.Acomp768) <
          reportedFailureBoundQ FIPS203.mlkem768 := by
  exact ⟨rfl, ConservativeBounds.mlkem768_failureProbabilityComputed_with_compression_lt_reportedFailureBoundQ⟩

theorem importedINDCCA_mlkem1024_uses_local_failure_proxy :
    let bundle : IND_CCA FIPS203.mlkem1024 := ProofLine.importedEpisodeV FIPS203.mlkem1024
    bundle.decryptionFailure.bound.numericUpperBound = some (reportedFailureBoundQ FIPS203.mlkem1024) ∧
      ConservativeBounds.failureProbabilityComputed FIPS203.mlkem1024
        (FIPS203.mlkem1024.k * FIPS203.mlkem1024.n)
        (ConservativeBounds.adjustedThreshold ConservativeBounds.Acomp1024) <
          reportedFailureBoundQ FIPS203.mlkem1024 := by
  exact ⟨rfl, ConservativeBounds.mlkem1024_failureProbabilityComputed_with_compression_lt_reportedFailureBoundQ⟩

end Security

end KEM
end Crypto
end HeytingLean
