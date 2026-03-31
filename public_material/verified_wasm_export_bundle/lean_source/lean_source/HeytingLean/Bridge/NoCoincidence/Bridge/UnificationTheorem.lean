import HeytingLean.Bridge.NoCoincidence.Nucleus.HeytingGapSoundness
import HeytingLean.Bridge.Wolfram.CausalInvariance
import HeytingLean.HossenfelderNoGo.HeytingBoundary.GapNonZero

namespace HeytingLean.Bridge.NoCoincidence.Bridge

open HeytingLean.Bridge.NoCoincidence.Nucleus
open HeytingLean.Bridge.Wolfram
open HeytingLean.HossenfelderNoGo.HeytingBoundary

/-- The imported Wolfram independence statement, named as a proposition rather than as a theorem
constant so it can appear directly inside conjunctions. -/
abbrev WolframIndependence : Prop :=
  (¬ (∀ {V P : Type} (sys : HeytingLean.WPP.Wolfram.System V P) [DecidableEq V],
      HeytingLean.WPP.Wolfram.Properties.ConfluentNF (sys := sys) →
        HeytingLean.WPP.Wolfram.Properties.CausalInvariant (sys := sys))) ∧
  (¬ (∀ {V P : Type} (sys : HeytingLean.WPP.Wolfram.System V P) [DecidableEq V],
      HeytingLean.WPP.Wolfram.Properties.CausalInvariant (sys := sys) →
        HeytingLean.WPP.Wolfram.Properties.ConfluentNF (sys := sys)))

/-- Imported Wolfram fact retained as a conceptual parallel. It is not a theorem about circuit
nuclei and is therefore kept separate from the genuine circuit consequence theorem below. -/
theorem wolfram_independence_parallel : WolframIndependence := by
  exact HeytingLean.Bridge.Wolfram.confluence_causal_invariance_independent

/-- Genuine formal consequence for the circuit lane: a nonempty circuit Heyting gap forces a
non-Boolean boundary nucleus. Wolfram independence and the sheaf-neural bridge remain parallels,
not formal consequences of this theorem. -/
theorem circuit_heyting_gap_and_non_boolean
    {n : ℕ}
    (R : CircuitNucleus n)
    (P : CircuitProp n)
    (hGap : ∃ C, C ∈ circuitHeytingGap R P)
    (hBridge : BooleanBoundaryBridge (circuitBoundaryNucleus R)) :
    boundaryGap (circuitBoundaryNucleus R) P ≠ ∅ ∧
    ¬ isBoolean (circuitBoundaryNucleus R) := by
  exact ⟨circuit_boundary_gap_nonempty R P hGap, circuit_boundary_non_boolean R hBridge⟩

end HeytingLean.Bridge.NoCoincidence.Bridge
