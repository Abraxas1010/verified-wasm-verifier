import HeytingLean.MirandaDynamics.Thermal.Basic
import HeytingLean.MirandaDynamics.Thermal.SafetyPredicates
import HeytingLean.MirandaDynamics.Thermal.Certificate

/-!
# MirandaDynamics.Thermal: Physically Unclonable Function (PUF)

This file defines types and predicates for hardware device identity using
a PUF-like construction that combines:

1. **Static hardware identifiers**: GPU UUID, NVMe serial, MAC addresses, ConnectX GUIDs
2. **Thermal signature patterns**: Manufacturing-specific thermal response characteristics
3. **Challenge-response protocol**: For verification without revealing the fingerprint

The PUF provides cryptographic provenance from physical hardware through to
proof verification, establishing trust in the hardware running the system.

## References

- Physical Unclonable Functions: https://en.wikipedia.org/wiki/Physical_unclonable_function
- Silicon PUFs: https://doi.org/10.1145/586110.586132
- Thermal PUFs: https://doi.org/10.1109/HOST.2014.6855561
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Thermal

/-! ## Hardware Component Types -/

/-- Classification of hardware components that contribute to the PUF fingerprint. -/
inductive PufComponent where
  | machineId       -- Linux machine-id (persistent OS identifier)
  | gpuUuid         -- NVIDIA GPU UUID
  | nvmeSerial      -- NVMe drive serial number
  | macAddress      -- Network interface MAC address
  | connectXGuid    -- Mellanox ConnectX-7 GUID
  | thermalSignature -- Manufacturing-specific thermal patterns
  deriving Repr, DecidableEq

namespace PufComponent

def name : PufComponent → String
  | .machineId => "Machine ID"
  | .gpuUuid => "GPU UUID"
  | .nvmeSerial => "NVMe Serial"
  | .macAddress => "MAC Address"
  | .connectXGuid => "ConnectX GUID"
  | .thermalSignature => "Thermal Signature"

/-- Weight for component in fingerprint calculation (higher = more unique). -/
def weight : PufComponent → Float
  | .machineId => 0.15       -- Can be regenerated
  | .gpuUuid => 0.25         -- Factory-burned, highly unique
  | .nvmeSerial => 0.20      -- Factory-burned
  | .macAddress => 0.10      -- Can be spoofed, but useful
  | .connectXGuid => 0.15    -- Factory-burned
  | .thermalSignature => 0.15 -- Manufacturing variance

/-- Whether this component is factory-burned (cannot be changed). -/
def isImmutable : PufComponent → Bool
  | .machineId => false
  | .gpuUuid => true
  | .nvmeSerial => true
  | .macAddress => false
  | .connectXGuid => true
  | .thermalSignature => true

end PufComponent

/-! ## Hardware Identifier Structures -/

/-- A network interface with its MAC address. -/
structure MacAddressEntry where
  interface : String     -- e.g., "eth0", "enp1s0"
  mac : String           -- e.g., "00:11:22:33:44:55"
  deriving Repr

/-- A ConnectX-7 Infiniband interface with its GUID. -/
structure ConnectXEntry where
  device : String        -- e.g., "mlx5_0"
  guid : String          -- Node GUID
  deriving Repr

/-- Complete collection of hardware identifiers for PUF construction. -/
structure HardwareIdentifiers where
  machineId : Option String
  gpuUuid : Option String
  nvmeSerial : Option String
  macAddresses : List MacAddressEntry
  connectXGuids : List ConnectXEntry
  deriving Repr

namespace HardwareIdentifiers

/-- Count the number of valid (non-None) static identifiers. -/
def staticCount (h : HardwareIdentifiers) : Nat :=
  (if h.machineId.isSome then 1 else 0) +
  (if h.gpuUuid.isSome then 1 else 0) +
  (if h.nvmeSerial.isSome then 1 else 0) +
  h.macAddresses.length +
  h.connectXGuids.length

/-- Count immutable (factory-burned) identifiers. -/
def immutableCount (h : HardwareIdentifiers) : Nat :=
  (if h.gpuUuid.isSome then 1 else 0) +
  (if h.nvmeSerial.isSome then 1 else 0) +
  h.connectXGuids.length

end HardwareIdentifiers

/-! ## Thermal Signature Types -/

/-- Statistical summary of thermal variance for a zone.

Manufacturing differences cause subtle variations in thermal behavior
that create a unique "thermal fingerprint" for each device.
-/
structure ThermalVariance where
  mean : Float        -- Average temperature during baseline
  stdDev : Float      -- Standard deviation
  min : Float         -- Minimum observed
  max : Float         -- Maximum observed
  deriving Repr

/-- Complete thermal signature capturing manufacturing-specific patterns. -/
structure ThermalSignature where
  /-- Timestamp of signature collection (Unix ms). -/
  timestamp : Int
  /-- Baseline temperatures per zone. -/
  baseline : List (String × Float)  -- (zone_id, temp_c)
  /-- Variance statistics per zone. -/
  variance : List (String × ThermalVariance)
  /-- Number of samples used to compute variance. -/
  sampleCount : Nat
  deriving Repr

namespace ThermalSignature

/-- Get variance for a specific zone. -/
def getVariance (sig : ThermalSignature) (zoneId : String) : Option ThermalVariance :=
  sig.variance.find? (·.1 == zoneId) |>.map (·.2)

/-- Check if signature has sufficient samples for reliability. -/
def isReliable (sig : ThermalSignature) : Bool :=
  sig.sampleCount ≥ 5

end ThermalSignature

/-! ## PUF Fingerprint -/

/-- The complete PUF fingerprint combining all components.

The fingerprint is a SHA-256 hash of all hardware identifiers and
thermal signature data, providing a unique device identity.
-/
structure PufFingerprint where
  /-- Full SHA-256 fingerprint (64 hex characters). -/
  fingerprint : String
  /-- Short fingerprint for display (first 16 characters). -/
  fingerprintShort : String
  /-- Version of the PUF generation algorithm. -/
  version : String
  /-- Timestamp of fingerprint creation (ISO8601). -/
  created : String
  /-- Hardware identifiers used. -/
  hardware : HardwareIdentifiers
  /-- Thermal signature used. -/
  thermalSignature : ThermalSignature
  deriving Repr

namespace PufFingerprint

/-- Minimum fingerprint length for validity. -/
def minLength : Nat := 64

/-- Check if fingerprint has valid format. -/
def isValidFormat (fp : PufFingerprint) : Bool :=
  fp.fingerprint.length == minLength &&
  fp.fingerprintShort.length == 16

end PufFingerprint

/-! ## Verification Types -/

/-- Result of a single component verification check. -/
structure ComponentCheck where
  component : PufComponent
  passed : Bool
  expected : Option String
  actual : Option String
  deriving Repr

/-- Complete PUF verification result. -/
structure PufVerification where
  /-- Overall verification passed. -/
  verified : Bool
  /-- The fingerprint being verified. -/
  fingerprint : String
  /-- Short fingerprint. -/
  fingerprintShort : String
  /-- Individual component checks. -/
  checks : List ComponentCheck
  /-- Timestamp of verification. -/
  timestamp : String
  /-- Number of verifications performed on this device. -/
  verificationCount : Nat
  deriving Repr

namespace PufVerification

/-- Count how many checks passed. -/
def passedCount (v : PufVerification) : Nat :=
  v.checks.filter (·.passed) |>.length

/-- Count how many checks failed. -/
def failedCount (v : PufVerification) : Nat :=
  v.checks.filter (fun c => !c.passed) |>.length

/-- Verification confidence (0.0 to 1.0). -/
def confidence (v : PufVerification) : Float :=
  if v.checks.isEmpty then 0.0
  else Float.ofNat v.passedCount / Float.ofNat v.checks.length

end PufVerification

/-! ## Challenge-Response Protocol -/

/-- A challenge for the PUF challenge-response protocol.

The challenge includes a nonce to prevent replay attacks.
-/
structure PufChallenge where
  /-- Random nonce provided by verifier. -/
  challenge : String
  /-- Timestamp of challenge issuance. -/
  timestamp : String
  /-- Challenge expiration (seconds). -/
  expiresIn : Nat := 60
  deriving Repr

/-- Response to a PUF challenge.

The response incorporates:
1. The original challenge
2. The device fingerprint
3. Current thermal state (for freshness)
4. A computed response hash
-/
structure PufResponse where
  /-- Original challenge. -/
  challenge : String
  /-- Computed response (SHA-256 of challenge + fingerprint + thermal). -/
  response : String
  /-- Timestamp of response generation. -/
  timestamp : String
  /-- Current thermal snapshot for freshness. -/
  thermalSnapshot : ThermalState
  /-- Short fingerprint for identification. -/
  fingerprintShort : String
  deriving Repr

/-! ## Safety Predicates -/

/-- Predicate: Hardware identifiers are sufficient for PUF construction.

Requires at least 3 distinct identifiers with at least 2 being immutable.
-/
def SufficientHardware (h : HardwareIdentifiers) : Prop :=
  h.staticCount ≥ 3 ∧ h.immutableCount ≥ 2

/-- Predicate: Thermal signature is reliable for PUF use. -/
def ReliableThermalSignature (sig : ThermalSignature) : Prop :=
  sig.sampleCount ≥ 5 ∧ sig.variance.length ≥ 3

/-- Predicate: PUF fingerprint has valid format. -/
def ValidFingerprint (fp : PufFingerprint) : Prop :=
  fp.fingerprint.length == PufFingerprint.minLength ∧
  fp.fingerprintShort.length == 16

/-- Predicate: PUF verification succeeded with high confidence. -/
def HighConfidenceVerification (v : PufVerification) : Prop :=
  v.verified ∧ v.confidence ≥ 0.8

/-- Predicate: Challenge-response is valid (response matches expected). -/
def ValidChallengeResponse (challenge : PufChallenge) (response : PufResponse) : Prop :=
  challenge.challenge == response.challenge

/-! ## Decidable Checks -/

/-- Check if hardware is sufficient (decidable). -/
def isSufficientHardware (h : HardwareIdentifiers) : Bool :=
  h.staticCount ≥ 3 && h.immutableCount ≥ 2

/-- Check if thermal signature is reliable (decidable). -/
def isReliableThermalSignature (sig : ThermalSignature) : Bool :=
  sig.sampleCount ≥ 5 && sig.variance.length ≥ 3

/-- Check if fingerprint is valid (decidable). -/
def isValidFingerprint (fp : PufFingerprint) : Bool :=
  fp.fingerprint.length == PufFingerprint.minLength &&
  fp.fingerprintShort.length == 16

/-- Check if verification has high confidence (decidable). -/
def isHighConfidenceVerification (v : PufVerification) : Bool :=
  v.verified && v.confidence ≥ 0.8

/-! ## PUF Device Identity Certificate -/

/-- A complete PUF device identity certificate.

This certificate binds:
1. Hardware identifiers → device
2. Thermal signature → manufacturing characteristics
3. Fingerprint → unique device identity
4. Verification history → trust over time
-/
structure PufCertificate where
  /-- Unique certificate identifier. -/
  certificateId : String
  /-- Timestamp of certificate creation (ISO8601). -/
  timestamp : String
  /-- The device fingerprint. -/
  fingerprint : PufFingerprint
  /-- Most recent verification result. -/
  verification : Option PufVerification
  /-- Verification status. -/
  status : ProofStatus
  /-- Total number of successful verifications. -/
  totalVerifications : Nat
  deriving Repr

namespace PufCertificate

/-- Check if certificate is currently valid. -/
def isValid (cert : PufCertificate) : Bool :=
  cert.status == .verified &&
  (cert.verification.map (·.verified)).getD false

/-- Compute certificate status from verification. -/
def computeStatus (v : Option PufVerification) : ProofStatus :=
  match v with
  | none => .unverified
  | some verification =>
    if verification.verified && verification.confidence ≥ 0.8 then .verified
    else if verification.verified then .runtime
    else .failed

end PufCertificate

end Thermal
end MirandaDynamics
end HeytingLean
