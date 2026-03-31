import HeytingLean.Crypto.VerifiedPQC.RuntimeOps
import HeytingLean.Crypto.VerifiedPQC.Serialization

namespace HeytingLean
namespace Crypto
namespace VerifiedPQC

/-- Distinct operational paths used by the runtime interop audits. -/
inductive RuntimePath where
  | promotedRuntime
  | serializedEnvelope
  | exportedDriver
  deriving DecidableEq, Repr

def distinctPaths (producer consumer : RuntimePath) : Bool :=
  producer != consumer

def packetRoundtripOk (packet : Packet) : Bool :=
  let env := PacketEnvelope.ofPacket packet
  PacketEnvelope.fromBytes? env.toBytes == some env && env.matchesPacket packet

def replayGuardRejects (seen : List ByteArray) (digest : ByteArray) : Bool :=
  seen.contains digest

def freshnessGuardAccepts (currentTs maxAge ts : UInt64) : Bool :=
  ts + maxAge >= currentTs

def lineageGuardAccepts (expected actual : String) : Bool :=
  expected = actual

theorem distinctPaths_self_false (path : RuntimePath) :
    distinctPaths path path = false := by
  simp [distinctPaths]

end VerifiedPQC
end Crypto
end HeytingLean
