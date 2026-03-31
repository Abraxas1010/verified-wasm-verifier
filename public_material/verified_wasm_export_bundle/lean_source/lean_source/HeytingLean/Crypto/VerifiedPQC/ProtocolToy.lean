import HeytingLean.Crypto.VerifiedPQC.Protocol

namespace HeytingLean
namespace Crypto
namespace VerifiedPQC

/-- Toy ML-KEM backend kept only for scaffold tests and local sanity checks. -/
def protocolToyKEMOps : KEMOps where
  encap := KEM.Toy.encap
  decap := KEM.Toy.decap

/-- Toy ML-DSA backend kept only for scaffold tests and local sanity checks. -/
def protocolToyDSAOps : DSAOps where
  signAttached := DSA.Toy.signAttached
  openSignedMessage := DSA.Toy.openSignedMessage

/-- Scaffold-only send path backed by the toy executables. -/
def sendToy : ParameterBundle → KEM.PublicKey → DSA.SecretKey → ByteArray →
    CarriedCertificate → RNG.SeededRNG → Packet × RNG.SeededRNG :=
  sendWith protocolToyKEMOps protocolToyDSAOps

/-- Scaffold-only verification path backed by the toy executables. -/
def verifyPacketToy : ParameterBundle → DSA.PublicKey → KEM.SecretKey → Packet → VerificationReport :=
  verifyPacketWith protocolToyKEMOps protocolToyDSAOps

/-- Scaffold-only receive path backed by the toy executables. -/
def receiveToy : ParameterBundle → DSA.PublicKey → KEM.SecretKey → Packet →
    Except ReceiveError ByteArray :=
  receiveWith protocolToyKEMOps protocolToyDSAOps

end VerifiedPQC
end Crypto
end HeytingLean
