/-!
# MirandaDynamics.Thermal: basic types

This module provides an *observation-first* physical-system integration target for the DGX Spark
thermal monitoring system, designed for binding with Lean proof verification.

We intentionally separate:

- **data** (zones/samples/readings), which we can represent directly, from
- **physics claims** (thermal dynamics, heat transfer), which will be introduced only as
  explicit interfaces/structures elsewhere.

The corresponding data acquisition bridge lives in `server/dgx-poller/`.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Thermal

/-- Classification of CPU core types on DGX Spark GB10. -/
inductive CoreClass where
  | x925_performance   -- Cortex-X925 performance cores
  | a725_efficiency    -- Cortex-A725 efficiency cores
  | gpu_compute        -- GB10 Blackwell GPU
  | soc_peripheral     -- SoC peripheral (VRM, I/O)
  | storage            -- NVMe storage
  | network            -- ConnectX-7 NIC
  deriving Repr, DecidableEq

namespace CoreClass

def name : CoreClass → String
  | .x925_performance => "Cortex-X925"
  | .a725_efficiency => "Cortex-A725"
  | .gpu_compute => "GB10 Blackwell"
  | .soc_peripheral => "SoC Peripheral"
  | .storage => "NVMe Storage"
  | .network => "ConnectX-7 NIC"

/-- Typical critical temperature threshold in Celsius. -/
def criticalTempC : CoreClass → Float
  | .x925_performance => 105.0
  | .a725_efficiency => 100.0
  | .gpu_compute => 100.0
  | .soc_peripheral => 95.0
  | .storage => 85.0
  | .network => 90.0

/-- Typical warning temperature threshold in Celsius. -/
def warningTempC : CoreClass → Float
  | .x925_performance => 95.0
  | .a725_efficiency => 90.0
  | .gpu_compute => 90.0
  | .soc_peripheral => 85.0
  | .storage => 75.0
  | .network => 80.0

end CoreClass

/-- A thermal zone with known identification and component mapping.

All numeric fields are kept as `Float` for practical JSON interoperability.
-/
structure ThermalZone where
  zoneId : String           -- e.g., "acpitz_temp1"
  component : String        -- e.g., "cpu_x925_cluster"
  coreClass : CoreClass
  confidence : Float        -- mapping confidence 0.0-1.0
  physicalHint : String     -- e.g., "Upper CPU region"
  deriving Repr

namespace ThermalZone

def key (z : ThermalZone) : String := z.zoneId

/-- The 12 thermal zones from DGX Spark thermal_zone_map.json -/
def dgxSparkZones : List ThermalZone := [
  { zoneId := "acpitz_temp1", component := "cpu_x925_cluster",
    coreClass := .x925_performance, confidence := 0.85, physicalHint := "Upper CPU region" },
  { zoneId := "acpitz_temp5", component := "cpu_x925_cluster",
    coreClass := .x925_performance, confidence := 0.85, physicalHint := "CPU die center" },
  { zoneId := "acpitz_temp3", component := "cpu_a725_cluster",
    coreClass := .a725_efficiency, confidence := 0.75, physicalHint := "Lower CPU region" },
  { zoneId := "acpitz_temp2", component := "cpu_peripheral",
    coreClass := .soc_peripheral, confidence := 0.70, physicalHint := "L3 cache area" },
  { zoneId := "acpitz_temp4", component := "cpu_peripheral",
    coreClass := .soc_peripheral, confidence := 0.70, physicalHint := "Memory controller" },
  { zoneId := "acpitz_temp6", component := "soc_vrm",
    coreClass := .soc_peripheral, confidence := 0.60, physicalHint := "Near fan exhaust" },
  { zoneId := "acpitz_temp7", component := "soc_io",
    coreClass := .soc_peripheral, confidence := 0.65, physicalHint := "Peripheral interconnect" },
  { zoneId := "gpu", component := "gpu_die",
    coreClass := .gpu_compute, confidence := 0.95, physicalHint := "GPU compute area" },
  { zoneId := "nvme_composite", component := "nvme_controller",
    coreClass := .storage, confidence := 0.90, physicalHint := "M.2 slot" },
  { zoneId := "nvme_sensor_1", component := "nvme_nand",
    coreClass := .storage, confidence := 0.85, physicalHint := "Storage chips" },
  { zoneId := "mlx5_3", component := "connectx7_port1",
    coreClass := .network, confidence := 0.90, physicalHint := "QSFP port area" },
  { zoneId := "mlx5_4", component := "connectx7_port2",
    coreClass := .network, confidence := 0.90, physicalHint := "QSFP port area" }
]

end ThermalZone

/-- A time window for an observation, expressed in Unix time (milliseconds). -/
structure ObservationWindow where
  start_time_ms : Int
  duration_ms : Int
  deriving Repr

/-- A single temperature sample at a point in time.

This is deliberately a "thin" container around temperature + timing metadata.
-/
structure ThermalSample where
  zone : ThermalZone
  tempC : Float            -- Temperature in Celsius
  timestamp_ms : Int       -- Unix timestamp in milliseconds
  deriving Repr

/-- Raw thermal reading data from multiple zones over a fixed window.

This parallels the Seismic.Waveform structure for continuous observation.
-/
structure ThermalReading where
  window : ObservationWindow
  samples : Array ThermalSample
  sample_rate_hz : Float        -- Polling rate (typically 1-10 Hz)
  deriving Repr

/-- System-wide thermal state at a single point in time.

Maps zone IDs to their current temperature readings.
-/
structure ThermalState where
  timestamp_ms : Int
  zones : List (String × Float)  -- (zone_id, temp_c) pairs
  gpuTempC : Option Float
  gpuPowerW : Option Float
  gpuUtilPct : Option Float
  deriving Repr

namespace ThermalState

def getZoneTemp (s : ThermalState) (zoneId : String) : Option Float :=
  s.zones.find? (fun p => p.1 == zoneId) |>.map (·.2)

def allZoneTemps (s : ThermalState) : List Float :=
  s.zones.map (·.2)

def maxTemp (s : ThermalState) : Option Float :=
  let temps := s.allZoneTemps
  if temps.isEmpty then none else some (temps.foldl max 0.0)

end ThermalState

end Thermal
end MirandaDynamics
end HeytingLean
