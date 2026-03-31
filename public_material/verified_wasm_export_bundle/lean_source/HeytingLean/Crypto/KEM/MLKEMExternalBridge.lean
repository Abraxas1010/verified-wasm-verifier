import HeytingLean.Crypto.KEM.MLKEMProofLine
import HeytingLean.Crypto.KEM.MLKEMSecurity

namespace HeytingLean
namespace Crypto
namespace KEM
namespace FIPS203
namespace ExternalBridge

/-- Checker-backed certificate for an imported external security claim. -/
structure BridgeCertificate where
  claimId : String
  sourceLabel : String
  sourceLocation : String
  checker : String
  evidencePath : String
  claimStatus : String
  boundary : String
  deriving Repr, DecidableEq

/-- Imported statement paired with an auditable bridge certificate. -/
structure BridgeCheckedStatement (α : Type) where
  certificate : BridgeCertificate
  statement : α

/-- Bridge-checked imported ML-KEM IND-CCA statement. -/
noncomputable def importedINDCCABridge (p : MLKEM203Params) :
    BridgeCheckedStatement (FIPS203.ProofLine.StatementBundle p) :=
  { certificate :=
      { claimId := s!"mlkem-ind-cca-{p.name}"
        sourceLabel := FIPS203.ProofLine.episodeVBundle.basePKE.label
        sourceLocation := FIPS203.ProofLine.episodeVBundle.basePKE.location
        checker := "python3 scripts/verified_pqc_external_bridge_audit.py --json"
        evidencePath := "artifacts/crypto/verified_pqc_external_bridge/"
        claimStatus := "bridge_checked"
        boundary := "Imported Episode V / FO proof line remains external; the repo-local bridge checks provenance and claim classification." }
    statement := FIPS203.ProofLine.importedEpisodeV p }

theorem importedINDCCABridge_status (p : MLKEM203Params) :
    (importedINDCCABridge p).certificate.claimStatus = "bridge_checked" := rfl

theorem importedINDCCABridge_statement (p : MLKEM203Params) :
    (importedINDCCABridge p).statement = FIPS203.ProofLine.importedEpisodeV p := rfl

end ExternalBridge
end FIPS203
end KEM
end Crypto
end HeytingLean
