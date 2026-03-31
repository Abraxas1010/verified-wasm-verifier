import HeytingLean.Physics.Channels.CPTP

/-!
# Photoemission (three-step model): task layer

This file introduces Malhotra’s three-step photoemission model at the level of
typed quantum channels:
1. absorption/excitation,
2. transport,
3. emission.

The physical details are recorded as `Prop` fields (interface-first). This lets
the project state and compose theorems without forcing a full analytic
formalization up front.
-/

noncomputable section

namespace HeytingLean
namespace Physics
namespace Photoemission

open HeytingLean.Physics.Substrate
open HeytingLean.Physics.Channels

/-- Hilbert spaces and basic distinguished states for a photoemission system. -/
structure PhotoemissionSystem where
  H_photon : HilbertSubstrate
  H_electron_bulk : HilbertSubstrate
  H_electron_surface : HilbertSubstrate
  H_electron_vacuum : HilbertSubstrate
  /-- Distinguished bulk ground state `|g⟩`. -/
  ground_state : Fin H_electron_bulk.dim
  /-- Distinguished bulk excited state `|e⟩`. -/
  excited_state : Fin H_electron_bulk.dim

namespace PhotoemissionSystem

/-- Input substrate for absorption: photon ⊗ bulk electron. -/
abbrev H_in_absorption (sys : PhotoemissionSystem) : HilbertSubstrate :=
  HilbertSubstrate.tensor sys.H_photon sys.H_electron_bulk

end PhotoemissionSystem

/-- Task 1: photon absorption and electron excitation. -/
structure AbsorptionTask (sys : PhotoemissionSystem) where
  channel : QuantumChannel (sys.H_in_absorption) sys.H_electron_bulk
  /-- Specification: the channel performs the intended excitation (interface-first). -/
  absorption_spec : Prop

/-- Task 2: electron transport (bulk → surface). -/
structure TransportTask (sys : PhotoemissionSystem) where
  channel : QuantumChannel sys.H_electron_bulk sys.H_electron_surface
  /-- Mean free path parameter (λ in the paper). -/
  mean_free_path : ℝ
  /-- Specification: attenuation/transport model holds (interface-first). -/
  attenuation_model : Prop

/-- Task 3: electron emission (surface → vacuum). -/
structure EmissionTask (sys : PhotoemissionSystem) where
  channel : QuantumChannel sys.H_electron_surface sys.H_electron_vacuum
  /-- Work function Φ. -/
  work_function : ℝ
  /-- Barrier width d. -/
  barrier_width : ℝ
  /-- Specification: WKB tunneling model holds (interface-first). -/
  wkb_transmission : Prop

/-- Sequential composition of the three-step photoemission channel. -/
def PhotoemissionChannel (sys : PhotoemissionSystem)
    (T₁ : AbsorptionTask sys) (T₂ : TransportTask sys) (T₃ : EmissionTask sys) :
    QuantumChannel sys.H_in_absorption sys.H_electron_vacuum :=
  QuantumChannel.comp T₃.channel (QuantumChannel.comp T₂.channel T₁.channel)

end Photoemission
end Physics
end HeytingLean

