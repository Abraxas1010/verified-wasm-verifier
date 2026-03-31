import HeytingLean.MirandaDynamics.TKFT.Reaching
import HeytingLean.MirandaDynamics.Seismic.Basic

/-!
# MirandaDynamics.Seismic: reaching semantics (interface-first)

This file defines a TKFT-style reaching relation derived from a **travel-time + detection** model.

We deliberately keep the physics content behind explicit *data interfaces* so that downstream
logical theorems are honest and auditable.

Concrete data acquisition is performed by `scripts/seismic_bridge.py`.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Seismic

open HeytingLean.MirandaDynamics.TKFT

/-- A minimal “travel time + tolerance” model.

This is where a real IASPEI91/TauP model would eventually be instantiated.
-/
structure TravelTimeModel where
  predicted_arrival_ms : SeismicEvent → Station → Int
  tolerance_ms : Int

/-- An observation/detection model, abstracted over the waveform acquisition mechanism.

`detect` is intended to mean “the event’s arrival is observed at the station”.
In practice this is a picking/threshold algorithm run against a waveform window.
-/
structure DetectionModel where
  /-- Executable detection predicate. -/
  detect : SeismicEvent → Waveform → Bool

/-- Seismic reaching: an event reaches a station if it is detected at that station.

This “reaching” is observational/epistemic: it is a predicate about what can be observed.
-/
def reaches (D : DetectionModel) (E : SeismicEvent) (W : Waveform) : Bool :=
  D.detect E W

/-- Package detection as a TKFT reaching relation.

Inputs are `(event, waveform)` pairs and outputs are the boolean “reached” observation.
This is a small, executable-friendly semantics layer.
-/
def reachingRelOfDetection (D : DetectionModel) :
    ReachingRel (SeismicEvent × Waveform) Bool :=
  ⟨fun inp out => out = reaches (D := D) inp.1 inp.2⟩

theorem reachingRelOfDetection_functional (D : DetectionModel) :
    (reachingRelOfDetection D).Functional := by
  intro inp b₁ b₂ h1 h2
  -- Both booleans are equal to the same RHS.
  exact h1.trans h2.symm

end Seismic
end MirandaDynamics
end HeytingLean
