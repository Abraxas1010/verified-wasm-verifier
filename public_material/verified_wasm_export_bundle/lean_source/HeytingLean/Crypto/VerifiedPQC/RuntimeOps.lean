import HeytingLean.Crypto.VerifiedPQC.Protocol
import HeytingLean.Crypto.VerifiedPQC.RuntimeBoundary
import HeytingLean.LeanCP.RealWorld.PQArithParams
import HeytingLean.LeanCP.RealWorld.MLDSAArithmeticVerified
import HeytingLean.LeanCP.RealWorld.MLKEMFOVerified

namespace HeytingLean
namespace Crypto
namespace VerifiedPQC

/-- Operational backend route for the promoted VerifiedPQC lane. -/
inductive BackendRoute where
  | pqcleanCli
  deriving DecidableEq, Repr

/-- Explicit operational backend descriptor for a promoted parameter bundle. -/
structure OperationalBackend where
  route : BackendRoute
  runtime : RuntimeBundle
  label : String
  deriving DecidableEq, Repr

/-- Promoted backend descriptor for the PQClean-backed operational lane. -/
def pqcleanBackend (bundle : ParameterBundle) : OperationalBackend :=
  { route := .pqcleanCli
    runtime := standardRuntimeBundle bundle
    label := s!"{(standardRuntimeBundle bundle).kem.scheme}+{(standardRuntimeBundle bundle).dsa.scheme}" }

/-- Operational backend descriptors must name both standardized schemes. -/
def schemesPresent (backend : OperationalBackend) : Bool :=
  !backend.runtime.kem.scheme.isEmpty && !backend.runtime.dsa.scheme.isEmpty

/-- Promoted operational backend enriched with the local arithmetic and FO witness surfaces. -/
structure WitnessedOperationalBackend (bundle : ParameterBundle) where
  operational : OperationalBackend
  kemWitness : LeanCP.RealWorld.MLKEMFOVerified.DecapsulationWitness bundle.kem
  mlkemModulus :
    (LeanCP.RealWorld.pqArithOfMLKEM203 bundle.kem).q = 3329
  mldsaModulus :
    (LeanCP.RealWorld.MLDSAArithmeticVerified.params bundle.dsa).q = 8380417

/-- The PQClean-backed promoted lane now carries the imported FO witness and parameter witnesses. -/
noncomputable def pqcleanWitnessedBackend (bundle : ParameterBundle)
    (hKem : KEM.FIPS203.validParams bundle.kem)
    (hDsa : DSA.FIPS204.validParams bundle.dsa) :
    WitnessedOperationalBackend bundle :=
  { operational := pqcleanBackend bundle
    kemWitness := LeanCP.RealWorld.MLKEMFOVerified.witness bundle.kem
    mlkemModulus := by
      simpa [LeanCP.RealWorld.pqArithOfMLKEM203] using hKem.2.1
    mldsaModulus := by
      simpa [LeanCP.RealWorld.MLDSAArithmeticVerified.params] using hDsa.2.1 }

theorem pqcleanWitnessedBackend_operational (bundle : ParameterBundle)
    (hKem : KEM.FIPS203.validParams bundle.kem)
    (hDsa : DSA.FIPS204.validParams bundle.dsa) :
    (pqcleanWitnessedBackend bundle hKem hDsa).operational = pqcleanBackend bundle := rfl

/-- Runtime-backed operational send plan.

This is an explicit deployment request for the standardized PQClean lane, not a pure Lean
reimplementation of the external runtime call. The local ML-KEM evidence travels alongside the
runtime metadata so the promoted path cannot silently collapse back to the toy scaffold. -/
structure OperationalSendPlan (bundle : ParameterBundle) where
  backend : WitnessedOperationalBackend bundle
  recipientPublicKey : ByteArray
  senderSecretKey : ByteArray
  payload : ByteArray
  certificate : CarriedCertificate

/-- Runtime-backed operational verification plan. -/
structure OperationalVerifyPlan (bundle : ParameterBundle) where
  backend : WitnessedOperationalBackend bundle
  senderPublicKey : ByteArray
  recipientSecretKey : ByteArray
  packetBytes : ByteArray

/-- Runtime-backed operational receive plan. -/
structure OperationalReceivePlan (bundle : ParameterBundle) where
  backend : WitnessedOperationalBackend bundle
  senderPublicKey : ByteArray
  recipientSecretKey : ByteArray
  packetBytes : ByteArray

/-- Build the promoted runtime send plan from a witnessed backend. -/
def sendOperational {bundle : ParameterBundle}
    (backend : WitnessedOperationalBackend bundle)
    (recipientPublicKey senderSecretKey payload : ByteArray)
    (certificate : CarriedCertificate) :
    OperationalSendPlan bundle :=
  { backend := backend
    recipientPublicKey := recipientPublicKey
    senderSecretKey := senderSecretKey
    payload := payload
    certificate := certificate }

/-- Build the promoted runtime verification plan from a witnessed backend. -/
def verifyOperational {bundle : ParameterBundle}
    (backend : WitnessedOperationalBackend bundle)
    (senderPublicKey recipientSecretKey packetBytes : ByteArray) :
    OperationalVerifyPlan bundle :=
  { backend := backend
    senderPublicKey := senderPublicKey
    recipientSecretKey := recipientSecretKey
    packetBytes := packetBytes }

/-- Build the promoted runtime receive plan from a witnessed backend. -/
def receiveOperational {bundle : ParameterBundle}
    (backend : WitnessedOperationalBackend bundle)
    (senderPublicKey recipientSecretKey packetBytes : ByteArray) :
    OperationalReceivePlan bundle :=
  { backend := backend
    senderPublicKey := senderPublicKey
    recipientSecretKey := recipientSecretKey
    packetBytes := packetBytes }

end VerifiedPQC
end Crypto
end HeytingLean
