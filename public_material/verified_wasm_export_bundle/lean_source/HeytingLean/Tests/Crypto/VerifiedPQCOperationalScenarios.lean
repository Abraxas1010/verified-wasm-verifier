import HeytingLean.Crypto.VerifiedPQC.RuntimeInterop

namespace HeytingLean.Tests.Crypto.VerifiedPQCOperationalScenarios

open HeytingLean
open HeytingLean.Crypto
open HeytingLean.Crypto.VerifiedPQC

def digestA : ByteArray := "digest-a".toUTF8

def replayScenarioRejects : Bool :=
  replayGuardRejects [digestA] digestA

def staleCertificateRejects : Bool :=
  freshnessGuardAccepts 20260327 30 20250000 = false

def downgradedBundleRejects : Bool :=
  distinctPaths .promotedRuntime .serializedEnvelope

def mixedLineageRejects : Bool :=
  lineageGuardAccepts "expected" "actual" = false

example : replayScenarioRejects = true := by
  native_decide

example : staleCertificateRejects = true := by
  native_decide

example : downgradedBundleRejects = true := by
  native_decide

example : mixedLineageRejects = true := by
  native_decide

end HeytingLean.Tests.Crypto.VerifiedPQCOperationalScenarios
