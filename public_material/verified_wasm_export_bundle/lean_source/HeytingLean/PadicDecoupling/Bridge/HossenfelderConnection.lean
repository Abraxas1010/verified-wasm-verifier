import HeytingLean.PadicDecoupling.Nucleus.GapAtDepth
import HeytingLean.HossenfelderNoGo.HeytingBoundary.GapNonZero

noncomputable section

namespace HeytingLean.PadicDecoupling.Bridge

open Set
open HeytingLean.HossenfelderNoGo.HeytingBoundary
open HeytingLean.PadicDecoupling.Nucleus

variable (p : ℕ) [Fact p.Prime]

abbrev padicBoundaryNucleus (k : ℕ) :
    BoundaryNucleus (DepthState p) :=
  padicDepthNucleus p k

theorem padic_boundary_non_boolean (k : ℕ)
    (hBridge : BooleanBoundaryBridge (padicBoundaryNucleus p k)) :
    ¬ isBoolean (padicBoundaryNucleus p k) :=
  boundary_necessarily_non_boolean (padicBoundaryNucleus p k) hBridge

theorem padic_boundary_gap_nonempty (k : ℕ) :
    ∃ S : DepthState p, boundaryGap (padicBoundaryNucleus p k) S ≠ ∅ := by
  obtain ⟨S, hne⟩ := gap_nonzero_at_finite_depth (p := p) k
  refine ⟨S, ?_⟩
  intro hGap
  have hmem : (padicBoundaryNucleus p k).R S ∈ boundaryGap (padicBoundaryNucleus p k) S := by
    simp [boundaryGap, hne]
  simp [hGap] at hmem

theorem hossenfelder_constrains_padic_depth (k : ℕ) :
    ∃ S : DepthState p, boundaryGap (padicBoundaryNucleus p k) S ≠ ∅ :=
  padic_boundary_gap_nonempty (p := p) k

end HeytingLean.PadicDecoupling.Bridge
