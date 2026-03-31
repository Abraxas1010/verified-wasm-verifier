import HeytingLean.Crypto.VerifiedPQC.RuntimeOps

namespace HeytingLean
namespace Crypto
namespace KEM

open VerifiedPQC

/-- Protocol-level witness for the promoted ML-KEM runtime lane.

This packages the standardized runtime metadata together with the local FO witness and the shared
arithmetic witnesses. It is intentionally a witness layer, not a fake pure Lean serializer for the
external ML-KEM runtime boundary. -/
structure PromotedProtocolWitness (bundle : ParameterBundle) where
  backend : WitnessedOperationalBackend bundle
  foParameterSet : backend.kemWitness.importedINDCCA.parameterSet = bundle.kem.name

/-- Build the protocol-level witness for the promoted runtime lane. -/
noncomputable def promotedProtocolWitness (bundle : ParameterBundle)
    (hKem : FIPS203.validParams bundle.kem)
    (hDsa : DSA.FIPS204.validParams bundle.dsa) :
    PromotedProtocolWitness bundle :=
  { backend := pqcleanWitnessedBackend bundle hKem hDsa
    foParameterSet := by
      simpa [pqcleanWitnessedBackend] using
        LeanCP.RealWorld.MLKEMFOVerified.witness_parameterSet bundle.kem }

theorem promotedProtocolWitness_route (bundle : ParameterBundle)
    (hKem : FIPS203.validParams bundle.kem)
    (hDsa : DSA.FIPS204.validParams bundle.dsa) :
    (promotedProtocolWitness bundle hKem hDsa).backend.operational.route = .pqcleanCli := rfl

theorem promotedProtocolWitness_mlkemModulus (bundle : ParameterBundle)
    (hKem : FIPS203.validParams bundle.kem)
    (hDsa : DSA.FIPS204.validParams bundle.dsa) :
    (promotedProtocolWitness bundle hKem hDsa).backend.mlkemModulus =
      (by simpa [LeanCP.RealWorld.pqArithOfMLKEM203] using hKem.2.1) := rfl

theorem promotedProtocolWitness_mldsaModulus (bundle : ParameterBundle)
    (hKem : FIPS203.validParams bundle.kem)
    (hDsa : DSA.FIPS204.validParams bundle.dsa) :
    (promotedProtocolWitness bundle hKem hDsa).backend.mldsaModulus =
      (by simpa [LeanCP.RealWorld.MLDSAArithmeticVerified.params] using hDsa.2.1) := rfl

end KEM
end Crypto
end HeytingLean
