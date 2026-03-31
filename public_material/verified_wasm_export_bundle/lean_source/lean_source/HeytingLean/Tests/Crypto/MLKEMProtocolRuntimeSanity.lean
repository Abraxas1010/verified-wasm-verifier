import HeytingLean.Crypto.KEM.MLKEMProtocolRuntime
import HeytingLean.Crypto.DSA.MLDSAStandardRuntime
import HeytingLean.Crypto.VerifiedPQC.CertificateRuntime

namespace HeytingLean.Tests.Crypto.MLKEMProtocolRuntimeSanity

open HeytingLean.Crypto

def sampleBundle : VerifiedPQC.ParameterBundle :=
  { kem := KEM.FIPS203.mlkem768
    dsa := DSA.FIPS204.mldsa65 }

#check KEM.runtimeKeygen
#check DSA.FIPS204.StandardRuntime.keygenSignAttached
#check DSA.FIPS204.StandardRuntime.keygenSignDetached
#check DSA.FIPS204.StandardRuntime.openSignedMessage
#check DSA.FIPS204.StandardRuntime.verifyDetached
#check DSA.FIPS204.StandardRuntime.publicKeyBytes
#check DSA.FIPS204.StandardRuntime.secretKeyBytes
#check DSA.FIPS204.StandardRuntime.detachedSignatureBytes
#check DSA.FIPS204.StandardRuntime.checkDetachedSignature
#check DSA.FIPS204.StandardRuntime.attachSignature
#check DSA.FIPS204.StandardRuntime.splitDetachedSignature?
#check VerifiedPQC.signCertificateWithStandardRuntime
#check VerifiedPQC.verifySignedCertificateWithStandardRuntime
#check KEM.sendWithStandardRuntime
#check KEM.sendWithAuthenticatedCertificateRuntime
#check KEM.verifyPacketWithStandardRuntime
#check KEM.verifyAuthenticatedPacketWithStandardRuntime
#check KEM.receiveWithStandardRuntime
#check KEM.receiveAuthenticatedWithStandardRuntime
#check KEM.runtimeRoundtrip
#check KEM.runtimeAuthenticatedRoundtrip

example :
    (VerifiedPQC.standardRuntimeBundle sampleBundle).kem.scheme = "ML-KEM-768" := by
  native_decide

example :
    (VerifiedPQC.standardRuntimeBundle sampleBundle).dsa.scheme = "ML-DSA-65" := by
  native_decide

example : DSA.FIPS204.StandardRuntime.publicKeyBytes DSA.FIPS204.mldsa65 = 1952 := by
  native_decide

example : DSA.FIPS204.StandardRuntime.secretKeyBytes DSA.FIPS204.mldsa65 = 4032 := by
  native_decide

example : DSA.FIPS204.StandardRuntime.detachedSignatureBytes DSA.FIPS204.mldsa65 = 3309 := by
  native_decide

example :
    DSA.FIPS204.StandardRuntime.checkDetachedSignature
      DSA.FIPS204.mldsa65
      (ByteArray.mk
        (Array.replicate
          (DSA.FIPS204.StandardRuntime.detachedSignatureBytes DSA.FIPS204.mldsa65) 0)) = true := by
  native_decide

example :
    KEM.authenticatedDecision 1 true true = 1 := by
  native_decide

example :
    KEM.authenticatedDecision 0 true true = 0 := by
  native_decide

end HeytingLean.Tests.Crypto.MLKEMProtocolRuntimeSanity
