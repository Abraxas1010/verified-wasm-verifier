import HeytingLean.MirandaDynamics.Thermal.Basic
import HeytingLean.MirandaDynamics.Thermal.SafetyPredicates
import HeytingLean.MirandaDynamics.Thermal.HardwareLedger
import HeytingLean.MirandaDynamics.Thermal.Observable
import HeytingLean.MirandaDynamics.Thermal.Reaching
import HeytingLean.MirandaDynamics.Thermal.Certificate
import HeytingLean.MirandaDynamics.Thermal.Autotune
import HeytingLean.MirandaDynamics.Thermal.PUF
import HeytingLean.MirandaDynamics.Thermal.Entropy

/-!
# MirandaDynamics.Thermal: barrel import

This module provides observation-first integration with the DGX Spark thermal monitoring system,
designed for binding runtime thermal data with Lean formal verification.

## Structure

- `Basic`: Core types (ThermalZone, ThermalSample, ThermalState, CoreClass)
- `SafetyPredicates`: Safety bounds and predicates (SafeTemp, SafeRate, SafeReading)
- `Observable`: Observation kernel for thermal windows (epistemological limits)
- `Reaching`: TKFT-style reaching relations for thermal state transitions
- `Certificate`: Verification certificates for proof binding
- `PUF`: Physically Unclonable Function for hardware device identity
- `Entropy`: Thermodynamic entropy source for TRNG and probability distributions
-/
