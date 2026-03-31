import HeytingLean.Crypto.DSA.MLDSASecurity

namespace HeytingLean
namespace Crypto
namespace DSA
namespace FIPS204
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

/-- Bridge-checked imported ML-DSA EUF-CMA statement. -/
def importedEUFCMABridge (p : MLDSAParams) :
    BridgeCheckedStatement (Security.EUF_CMA p) :=
  { certificate :=
      { claimId := s!"mldsa-euf-cma-{p.name}"
        sourceLabel := ProofLine.importedMLDSAReference.label
        sourceLocation := ProofLine.importedMLDSAReference.location
        checker := "python3 scripts/verified_pqc_external_bridge_audit.py --json"
        evidencePath := "artifacts/crypto/verified_pqc_external_bridge/"
        claimStatus := "bridge_checked"
        boundary := "Imported ML-DSA / Dilithium proof literature remains external; the repo-local bridge checks provenance and claim classification." }
    statement := ProofLine.importedStatementBundle (Security.toFIPS204Params p) }

theorem importedEUFCMABridge_status (p : MLDSAParams) :
    (importedEUFCMABridge p).certificate.claimStatus = "bridge_checked" := rfl

theorem importedEUFCMABridge_statement (p : MLDSAParams) :
    (importedEUFCMABridge p).statement = ProofLine.importedStatementBundle (Security.toFIPS204Params p) := rfl

end ExternalBridge
end FIPS204
end DSA
end Crypto
end HeytingLean
