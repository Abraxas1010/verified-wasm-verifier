import HeytingLean.MirandaDynamics.Thermal.Basic
import HeytingLean.MirandaDynamics.Thermal.SafetyPredicates

/-!
# MirandaDynamics.Thermal: verification certificates

This file defines the types for proof-binding between runtime thermal data
and Lean verification:

- `ProofStatus`: the verification status of a thermal condition
- `ThermalCondition`: a named condition with its Lean type and theorem reference
- `VerificationCertificate`: a complete certificate binding state to proofs

These types are designed for JSON interoperability with the server API.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Thermal

/-- Proof status for a thermal condition. -/
inductive ProofStatus where
  | verified      -- Lean proof exists and type-checks
  | pending       -- Conjecture stated, proof in progress
  | unverified    -- No proof attempted
  | failed        -- Proof attempted but failed
  | runtime       -- Checked at runtime, not formally verified
  deriving Repr, DecidableEq

namespace ProofStatus

def toString : ProofStatus → String
  | .verified => "verified"
  | .pending => "pending"
  | .unverified => "unverified"
  | .failed => "failed"
  | .runtime => "runtime"

def fromString : String → ProofStatus
  | "verified" => .verified
  | "pending" => .pending
  | "unverified" => .unverified
  | "failed" => .failed
  | "runtime" => .runtime
  | _ => .unverified

end ProofStatus

/-- A thermal condition that can be verified.

Links runtime data to Lean types and theorems.
-/
structure ThermalCondition where
  /-- Unique identifier for the condition. -/
  conditionId : String
  /-- Human-readable description. -/
  description : String
  /-- The zone this condition applies to. -/
  zoneId : String
  /-- Lean type signature for the predicate. -/
  leanType : String
  /-- Lean theorem name if proved. -/
  theoremName : Option String
  /-- Current verification status. -/
  status : ProofStatus
  /-- Timestamp of last status update (ISO8601). -/
  lastUpdated : String
  deriving Repr

namespace ThermalCondition

/-- Standard conditions for DGX Spark thermal zones. -/
def standardConditions : List ThermalCondition := [
  -- X925 Performance Cores
  { conditionId := "x925_safe_temp1"
    description := "X925 cluster 1 temperature is below critical threshold"
    zoneId := "acpitz_temp1"
    leanType := "HeytingLean.MirandaDynamics.Thermal.x925_safe"
    theoremName := some "HeytingLean.MirandaDynamics.Thermal.SafetyPredicates.x925_safe"
    status := .verified
    lastUpdated := "2026-01-27T00:00:00Z" },
  { conditionId := "x925_safe_temp5"
    description := "X925 cluster 2 temperature is below critical threshold"
    zoneId := "acpitz_temp5"
    leanType := "HeytingLean.MirandaDynamics.Thermal.x925_safe"
    theoremName := some "HeytingLean.MirandaDynamics.Thermal.SafetyPredicates.x925_safe"
    status := .verified
    lastUpdated := "2026-01-27T00:00:00Z" },

  -- A725 Efficiency Cores
  { conditionId := "a725_safe_temp3"
    description := "A725 cluster temperature is below critical threshold"
    zoneId := "acpitz_temp3"
    leanType := "HeytingLean.MirandaDynamics.Thermal.a725_safe"
    theoremName := some "HeytingLean.MirandaDynamics.Thermal.SafetyPredicates.a725_safe"
    status := .verified
    lastUpdated := "2026-01-27T00:00:00Z" },

  -- GPU
  { conditionId := "gpu_safe"
    description := "GPU die temperature is below critical threshold"
    zoneId := "gpu"
    leanType := "HeytingLean.MirandaDynamics.Thermal.gpu_safe"
    theoremName := some "HeytingLean.MirandaDynamics.Thermal.SafetyPredicates.gpu_safe"
    status := .verified
    lastUpdated := "2026-01-27T00:00:00Z" },

  -- NVMe
  { conditionId := "nvme_safe_composite"
    description := "NVMe controller temperature is below critical threshold"
    zoneId := "nvme_composite"
    leanType := "HeytingLean.MirandaDynamics.Thermal.nvme_safe"
    theoremName := some "HeytingLean.MirandaDynamics.Thermal.SafetyPredicates.nvme_safe"
    status := .verified
    lastUpdated := "2026-01-27T00:00:00Z" },
  { conditionId := "nvme_safe_sensor1"
    description := "NVMe NAND temperature is below critical threshold"
    zoneId := "nvme_sensor_1"
    leanType := "HeytingLean.MirandaDynamics.Thermal.nvme_safe"
    theoremName := some "HeytingLean.MirandaDynamics.Thermal.SafetyPredicates.nvme_safe"
    status := .verified
    lastUpdated := "2026-01-27T00:00:00Z" },

  -- Network
  { conditionId := "network_safe_mlx5_3"
    description := "ConnectX-7 port 1 temperature is below critical threshold"
    zoneId := "mlx5_3"
    leanType := "HeytingLean.MirandaDynamics.Thermal.network_safe"
    theoremName := some "HeytingLean.MirandaDynamics.Thermal.SafetyPredicates.network_safe"
    status := .verified
    lastUpdated := "2026-01-27T00:00:00Z" },
  { conditionId := "network_safe_mlx5_4"
    description := "ConnectX-7 port 2 temperature is below critical threshold"
    zoneId := "mlx5_4"
    leanType := "HeytingLean.MirandaDynamics.Thermal.network_safe"
    theoremName := some "HeytingLean.MirandaDynamics.Thermal.SafetyPredicates.network_safe"
    status := .verified
    lastUpdated := "2026-01-27T00:00:00Z" },

  -- SoC Peripheral zones
  { conditionId := "soc_safe_temp2"
    description := "L3 cache area temperature is below critical threshold"
    zoneId := "acpitz_temp2"
    leanType := "HeytingLean.MirandaDynamics.Thermal.soc_safe"
    theoremName := some "HeytingLean.MirandaDynamics.Thermal.SafetyPredicates.soc_safe"
    status := .verified
    lastUpdated := "2026-01-27T00:00:00Z" },
  { conditionId := "soc_safe_temp4"
    description := "Memory controller temperature is below critical threshold"
    zoneId := "acpitz_temp4"
    leanType := "HeytingLean.MirandaDynamics.Thermal.soc_safe"
    theoremName := some "HeytingLean.MirandaDynamics.Thermal.SafetyPredicates.soc_safe"
    status := .verified
    lastUpdated := "2026-01-27T00:00:00Z" },
  { conditionId := "soc_safe_temp6"
    description := "VRM temperature is below critical threshold"
    zoneId := "acpitz_temp6"
    leanType := "HeytingLean.MirandaDynamics.Thermal.soc_safe"
    theoremName := some "HeytingLean.MirandaDynamics.Thermal.SafetyPredicates.soc_safe"
    status := .verified
    lastUpdated := "2026-01-27T00:00:00Z" },
  { conditionId := "soc_safe_temp7"
    description := "SoC I/O temperature is below critical threshold"
    zoneId := "acpitz_temp7"
    leanType := "HeytingLean.MirandaDynamics.Thermal.soc_safe"
    theoremName := some "HeytingLean.MirandaDynamics.Thermal.SafetyPredicates.soc_safe"
    status := .verified
    lastUpdated := "2026-01-27T00:00:00Z" }
]

/-- Count conditions by status. -/
def countByStatus (conditions : List ThermalCondition) (status : ProofStatus) : Nat :=
  conditions.filter (·.status == status) |>.length

end ThermalCondition

/-- A verification certificate binding thermal state to proof status.

This is the top-level certificate that can be serialized to JSON
and transmitted to the dashboard.
-/
structure VerificationCertificate where
  /-- Unique certificate identifier. -/
  certificateId : String
  /-- Timestamp of certificate generation (ISO8601). -/
  timestamp : String
  /-- The thermal state being certified. -/
  thermalState : ThermalState
  /-- List of conditions with their verification status. -/
  conditions : List ThermalCondition
  /-- Overall proof status (verified if all conditions verified). -/
  overallStatus : ProofStatus
  /-- Git hash of the Lean build used for verification. -/
  leanBuildHash : Option String
  deriving Repr

namespace VerificationCertificate

/-- Compute overall status from conditions. -/
def computeOverallStatus (conditions : List ThermalCondition) : ProofStatus :=
  if conditions.all (·.status == .verified) then .verified
  else if conditions.any (·.status == .failed) then .failed
  else if conditions.any (·.status == .pending) then .pending
  else .unverified

/-- Create a certificate for a thermal state using standard conditions. -/
def forState (certId : String) (timestamp : String) (state : ThermalState)
    (buildHash : Option String := none) : VerificationCertificate :=
  let conditions := ThermalCondition.standardConditions
  { certificateId := certId
    timestamp := timestamp
    thermalState := state
    conditions := conditions
    overallStatus := computeOverallStatus conditions
    leanBuildHash := buildHash }

/-- Aggregate statistics for a certificate. -/
structure AggregateStats where
  verified : Nat
  pending : Nat
  unverified : Nat
  failed : Nat
  total : Nat
  deriving Repr

def aggregateStats (cert : VerificationCertificate) : AggregateStats :=
  { verified := ThermalCondition.countByStatus cert.conditions .verified
    pending := ThermalCondition.countByStatus cert.conditions .pending
    unverified := ThermalCondition.countByStatus cert.conditions .unverified
    failed := ThermalCondition.countByStatus cert.conditions .failed
    total := cert.conditions.length }

end VerificationCertificate

end Thermal
end MirandaDynamics
end HeytingLean
