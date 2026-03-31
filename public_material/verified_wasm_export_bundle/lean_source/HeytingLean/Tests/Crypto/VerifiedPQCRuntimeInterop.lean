import HeytingLean.Crypto.VerifiedPQC.RuntimeInterop

namespace HeytingLean.Tests.Crypto.VerifiedPQCRuntimeInterop

open HeytingLean
open HeytingLean.Crypto
open HeytingLean.Crypto.VerifiedPQC

def sampleBundle : ParameterBundle :=
  { kem := KEM.FIPS203.mlkem768
    dsa := DSA.FIPS204.mldsa65 }

def sampleBackend : OperationalBackend :=
  pqcleanBackend sampleBundle

example : sampleBackend.route = .pqcleanCli := by
  native_decide

example : schemesPresent sampleBackend = true := by
  native_decide

example : !(sampleBackend.runtime.kem.keygenCli.isEmpty) = true := by
  native_decide

example : !(sampleBackend.runtime.kem.encapCli.isEmpty) = true := by
  native_decide

example : !(sampleBackend.runtime.kem.decapDumpCli.isEmpty) = true := by
  native_decide

example : distinctPaths .promotedRuntime .serializedEnvelope = true := by
  native_decide

example : distinctPaths .serializedEnvelope .serializedEnvelope = false := by
  simp [distinctPaths]

example : freshnessGuardAccepts 20260327 30 20260327 = true := by
  native_decide

example : lineageGuardAccepts "lineage" "lineage" = true := by
  native_decide

end HeytingLean.Tests.Crypto.VerifiedPQCRuntimeInterop
