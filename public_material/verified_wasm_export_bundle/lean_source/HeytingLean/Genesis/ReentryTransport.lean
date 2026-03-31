import HeytingLean.Genesis.PlenumBridge
import HeytingLean.Genesis.CantorCutBridge
import HeytingLean.PerspectivalPlenum.DirectConnection

namespace HeytingLean.Genesis

open CategoryTheory
open PerspectivalPlenum
open scoped Classical

universe u v w

variable {Ωα : Type u} [HeytingLean.LoF.PrimaryAlgebra Ωα]
variable {C : Type v} [Category.{w} C]
variable [CategoryTheory.Limits.HasPullbacks C] [CategoryTheory.HasClassifier C]

/-- Concrete seed points for a chosen bridge instance. -/
structure ConcreteBridgeSeed
    (B : PerspectivalPlenum.ReentryLTBridge Ωα C) where
  stablePoint : Ωα
  unstablePoint : Ωα
  stable_fixed : B.R.nucleus stablePoint = stablePoint
  unstable_not_fixed : B.R.nucleus unstablePoint ≠ unstablePoint

/-- Concrete transport payload for `WitnessInterior` into the chosen bridge carrier. -/
noncomputable def witnessInterior_transport_data
    (B : PerspectivalPlenum.ReentryLTBridge Ωα C)
    (seed : ConcreteBridgeSeed B)
    (W : WitnessInterior) : Ωα := by
  classical
  exact if eventualStabilizes W.source then seed.stablePoint else seed.unstablePoint

@[simp] theorem witnessInterior_transport_data_stable
    (B : PerspectivalPlenum.ReentryLTBridge Ωα C)
    (seed : ConcreteBridgeSeed B)
    (W : WitnessInterior)
    (hW : eventualStabilizes W.source) :
    witnessInterior_transport_data B seed W = seed.stablePoint := by
  classical
  simp [witnessInterior_transport_data, hW]

@[simp] theorem witnessInterior_transport_data_unstable
    (B : PerspectivalPlenum.ReentryLTBridge Ωα C)
    (seed : ConcreteBridgeSeed B)
    (W : WitnessInterior)
    (hW : ¬ eventualStabilizes W.source) :
    witnessInterior_transport_data B seed W = seed.unstablePoint := by
  classical
  simp [witnessInterior_transport_data, hW]

/-- Stabilized witnesses map to `R`-fixed points under the concrete adapter. -/
theorem transport_stable_fixed
    (B : PerspectivalPlenum.ReentryLTBridge Ωα C)
    (seed : ConcreteBridgeSeed B)
    (W : WitnessInterior)
    (hW : eventualStabilizes W.source) :
    B.R.nucleus (witnessInterior_transport_data B seed W)
      = witnessInterior_transport_data B seed W := by
  classical
  simp [witnessInterior_transport_data, hW, seed.stable_fixed]

/-- Unstable witnesses map to non-fixed points under the concrete adapter. -/
theorem transport_unstable_not_fixed
    (B : PerspectivalPlenum.ReentryLTBridge Ωα C)
    (seed : ConcreteBridgeSeed B)
    (W : WitnessInterior)
    (hW : ¬ eventualStabilizes W.source) :
    B.R.nucleus (witnessInterior_transport_data B seed W)
      ≠ witnessInterior_transport_data B seed W := by
  classical
  simpa [witnessInterior_transport_data, hW] using seed.unstable_not_fixed

/-- Concrete Phase-7 bridge: stabilized transport points are LT-closed at `Ω`. -/
theorem transport_reentry_fixed_to_closed
    (B : PerspectivalPlenum.ReentryLTBridge Ωα C)
    (seed : ConcreteBridgeSeed B)
    (W : WitnessInterior)
    (hW : eventualStabilizes W.source) :
    HeytingLean.Topos.LocalOperator.IsClosed
      (C := C)
      (PerspectivalPlenum.ReentryLTBridge.localOperator (C := C) B)
      (B.truthEquiv (witnessInterior_transport_data B seed W)) := by
  exact
    PerspectivalPlenum.ReentryLTBridge.map_reentry_fixed_to_closed
      (C := C) (B := B)
      (hp := transport_stable_fixed (B := B) (seed := seed) (W := W) hW)

/-- Closed transport points recover re-entry fixedness. -/
theorem transport_closed_to_reentry_fixed
    (B : PerspectivalPlenum.ReentryLTBridge Ωα C)
    (seed : ConcreteBridgeSeed B)
    (W : WitnessInterior)
    (hClosed : HeytingLean.Topos.LocalOperator.IsClosed
      (C := C)
      (PerspectivalPlenum.ReentryLTBridge.localOperator (C := C) B)
      (B.truthEquiv (witnessInterior_transport_data B seed W))) :
    B.R.nucleus (witnessInterior_transport_data B seed W)
      = witnessInterior_transport_data B seed W := by
  exact
    PerspectivalPlenum.ReentryLTBridge.closed_to_reentry_fixed
      (C := C) (B := B) (hp := hClosed)

/-- Compatibility law for the concrete adapter: stabilization iff fixedness. -/
theorem transport_compat_with_stabilization
    (B : PerspectivalPlenum.ReentryLTBridge Ωα C)
    (seed : ConcreteBridgeSeed B)
    (W : WitnessInterior) :
    eventualStabilizes W.source ↔
      B.R.nucleus (witnessInterior_transport_data B seed W)
        = witnessInterior_transport_data B seed W := by
  constructor
  · intro hW
    exact transport_stable_fixed (B := B) (seed := seed) (W := W) hW
  · intro hFixed
    by_cases hW : eventualStabilizes W.source
    · exact hW
    · exact False.elim ((transport_unstable_not_fixed (B := B) (seed := seed) (W := W) hW) hFixed)

/-- Concrete emergent-region transport driven by stabilization, for phase-7 integration. -/
def emergent_region_transport_data (W : WitnessInterior) : EmergentRegion :=
  if eventualStabilizes W.source then minimalDistinction else (⊥ : EmergentRegion)

theorem emergent_region_transport_stable_fixed
    (W : WitnessInterior)
    (hW : eventualStabilizes W.source) :
    regionNucleus (emergent_region_transport_data W) = emergent_region_transport_data W := by
  calc
    regionNucleus (emergent_region_transport_data W)
        = regionNucleus minimalDistinction := by simp [emergent_region_transport_data, hW]
    _ = minimalDistinction := by
      rw [minimalDistinction_eq_singleton]
      ext x
      simp [regionNucleus_apply]
    _ = emergent_region_transport_data W := by simp [emergent_region_transport_data, hW]

theorem emergent_region_transport_unstable_not_fixed
    (W : WitnessInterior)
    (hW : ¬ eventualStabilizes W.source) :
    regionNucleus (emergent_region_transport_data W) ≠ emergent_region_transport_data W := by
  intro hEq
  have hmem : anchorClass ∈ regionNucleus (emergent_region_transport_data W) := by
    simp [emergent_region_transport_data, hW, regionNucleus_apply]
  have hnot : anchorClass ∉ emergent_region_transport_data W := by
    simp [emergent_region_transport_data, hW]
  exact hnot (hEq ▸ hmem)

theorem emergent_region_transport_compat_with_stabilization
    (W : WitnessInterior) :
    eventualStabilizes W.source ↔
      regionNucleus (emergent_region_transport_data W) = emergent_region_transport_data W := by
  constructor
  · intro hW
    exact emergent_region_transport_stable_fixed W hW
  · intro hFixed
    by_cases hW : eventualStabilizes W.source
    · exact hW
    · exact False.elim ((emergent_region_transport_unstable_not_fixed W hW) hFixed)

theorem emergent_region_transport_life_not_fixed :
    regionNucleus (emergent_region_transport_data (lifeInterior 0))
      ≠ emergent_region_transport_data (lifeInterior 0) := by
  exact emergent_region_transport_unstable_not_fixed (lifeInterior 0) life_not_eventualStabilizes

theorem emergent_region_transport_cantor_true_fixed
    (p : EvalPath) (h0 : p 0 = true) :
    regionNucleus (emergent_region_transport_data (cantorCut_to_witnessInterior p 0))
      = emergent_region_transport_data (cantorCut_to_witnessInterior p 0) := by
  exact emergent_region_transport_stable_fixed (cantorCut_to_witnessInterior p 0)
    ((cantorCut_transport_ready p 0).2 h0)

theorem emergent_region_transport_cantor_false_not_fixed
    (p : EvalPath) (h0 : p 0 = false) :
    regionNucleus (emergent_region_transport_data (cantorCut_to_witnessInterior p 0))
      ≠ emergent_region_transport_data (cantorCut_to_witnessInterior p 0) := by
  have hns : ¬ eventualStabilizes (cantorCut_to_witnessInterior p 0).source := by
    intro hs
    have htrue : p 0 = true := (cantorCut_transport_ready p 0).1 hs
    simp [h0] at htrue
  exact emergent_region_transport_unstable_not_fixed (cantorCut_to_witnessInterior p 0) hns

/-- Cantor-cut specialization: transport data is classified by the head bit. -/
theorem cantorCut_transport_data
    (B : PerspectivalPlenum.ReentryLTBridge Ωα C)
    (seed : ConcreteBridgeSeed B)
    (p : EvalPath)
    (depth : Nat) :
    witnessInterior_transport_data B seed (cantorCut_to_witnessInterior p depth)
      = (if p 0 then seed.stablePoint else seed.unstablePoint) := by
  classical
  cases h0 : p 0 with
  | false =>
      have hns : ¬ eventualStabilizes (cantorCut_to_witnessInterior p depth).source := by
        intro hs
        have htrue : p 0 = true := (cantorCut_transport_ready p depth).1 hs
        simp [h0] at htrue
      have hLife : ¬ eventualStabilizes CoGame.Life := by
        simpa [cantorCut_to_witnessInterior, headWitnessSource, h0] using hns
      simp [witnessInterior_transport_data, cantorCut_to_witnessInterior, headWitnessSource, h0, hLife]
  | true =>
      have hs : eventualStabilizes (cantorCut_to_witnessInterior p depth).source :=
        (cantorCut_transport_ready p depth).2 (by simp [h0])
      have hVoid : eventualStabilizes CoGame.Void := by
        simpa [cantorCut_to_witnessInterior, headWitnessSource, h0] using hs
      simp [witnessInterior_transport_data, cantorCut_to_witnessInterior, headWitnessSource, h0, hVoid]

end HeytingLean.Genesis
