import HeytingLean.Physics.Photoemission.Tasks
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Photoemission efficiency (η = A · T · D)

We work with the three-step photoemission channel layer (`Tasks.lean`) and
define “success probability” for a channel relative to a projector.  The key
factorization theorem is stated under an explicit *Markov/independence*
assumption packaged as a `Prop` record; this keeps the development
interface-first while supporting downstream reuse.
-/

noncomputable section

namespace HeytingLean
namespace Physics
namespace Photoemission

open HeytingLean.Physics.Substrate
open HeytingLean.Physics.Channels
open HeytingLean.Quantum
open Matrix

namespace Channels.QuantumChannel

variable {H_in H_out : HilbertSubstrate}

/-- Success probability of a channel on `ρ_in` with respect to a projector `Π`. -/
def successProbability (E : QuantumChannel H_in H_out)
    (ρ_in : DensityMatrix H_in)
    (projector : Mat H_out.dim) : ℝ :=
  (Matrix.trace (projector * (E.apply ρ_in).mat)).re

end Channels.QuantumChannel

namespace Projector

/-- A basis-state projector (diagonal projector onto a distinguished basis vector). -/
def basis (H : HilbertSubstrate) (i : Fin H.dim) : Mat H.dim :=
  Matrix.diagonal fun j => if j = i then (1 : ℂ) else 0

end Projector

/-- Projector onto the excited bulk state. -/
def excitedStateProjector (sys : PhotoemissionSystem) : Mat sys.H_electron_bulk.dim :=
  Projector.basis sys.H_electron_bulk sys.excited_state

/-- Surface detection projector (interface-first: identity means “any detected surface electron”). -/
def surfaceProjector (sys : PhotoemissionSystem) : Mat sys.H_electron_surface.dim :=
  (1 : Mat sys.H_electron_surface.dim)

/-- Vacuum detection projector (interface-first: identity means “any emitted electron detected”). -/
def vacuumProjector (sys : PhotoemissionSystem) : Mat sys.H_electron_vacuum.dim :=
  (1 : Mat sys.H_electron_vacuum.dim)

/-- Absorption probability `A`. -/
def absorptionProbability (sys : PhotoemissionSystem) (T₁ : AbsorptionTask sys)
    (ρ_in : DensityMatrix (sys.H_in_absorption)) : ℝ :=
  Channels.QuantumChannel.successProbability T₁.channel ρ_in (excitedStateProjector sys)

/-- Transport probability `T`. -/
def transportProbability (sys : PhotoemissionSystem) (T₂ : TransportTask sys)
    (ρ_exc : DensityMatrix sys.H_electron_bulk) : ℝ :=
  Channels.QuantumChannel.successProbability T₂.channel ρ_exc (surfaceProjector sys)

/-- Emission/detection probability `D`. -/
def emissionProbability (sys : PhotoemissionSystem) (T₃ : EmissionTask sys)
    (ρ_surface : DensityMatrix sys.H_electron_surface) : ℝ :=
  Channels.QuantumChannel.successProbability T₃.channel ρ_surface (vacuumProjector sys)

/-- Overall efficiency η (channel-level, measured at vacuum detection). -/
def overallEfficiency (sys : PhotoemissionSystem)
    (T₁ : AbsorptionTask sys) (T₂ : TransportTask sys) (T₃ : EmissionTask sys)
    (ρ_in : DensityMatrix (sys.H_in_absorption)) : ℝ :=
  Channels.QuantumChannel.successProbability (PhotoemissionChannel sys T₁ T₂ T₃) ρ_in
    (vacuumProjector sys)

/-- Markov/independence assumption packaging the η = A · T · D factorization. -/
structure MarkovianTransport (sys : PhotoemissionSystem)
    (T₁ : AbsorptionTask sys) (T₂ : TransportTask sys) (T₃ : EmissionTask sys)
    (ρ_in : DensityMatrix (sys.H_in_absorption)) : Prop where
  factorization :
    let A := absorptionProbability sys T₁ ρ_in
    let Tr := transportProbability sys T₂ (T₁.channel.apply ρ_in)
    let D := emissionProbability sys T₃ (T₂.channel.apply (T₁.channel.apply ρ_in))
    let η := overallEfficiency sys T₁ T₂ T₃ ρ_in
    η = A * Tr * D

/--
Main theorem: efficiency factorization η = A · T · D under the Markov/independence assumption.
-/
theorem efficiency_factorization (sys : PhotoemissionSystem)
    (T₁ : AbsorptionTask sys) (T₂ : TransportTask sys) (T₃ : EmissionTask sys)
    (ρ_in : DensityMatrix (sys.H_in_absorption))
    (h_markov : MarkovianTransport sys T₁ T₂ T₃ ρ_in) :
    let A := absorptionProbability sys T₁ ρ_in
    let Tr := transportProbability sys T₂ (T₁.channel.apply ρ_in)
    let D := emissionProbability sys T₃ (T₂.channel.apply (T₁.channel.apply ρ_in))
    let η := overallEfficiency sys T₁ T₂ T₃ ρ_in
    η = A * Tr * D := by
  simpa using h_markov.factorization

end Photoemission
end Physics
end HeytingLean

