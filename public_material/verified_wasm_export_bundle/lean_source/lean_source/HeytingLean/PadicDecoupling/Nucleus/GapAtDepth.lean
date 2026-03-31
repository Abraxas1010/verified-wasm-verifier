import HeytingLean.PadicDecoupling.Nucleus.FixedPoints

noncomputable section

namespace HeytingLean.PadicDecoupling.Nucleus

open Set

variable (p : ℕ) [Fact p.Prime]

theorem witness_outside_roundedSkeleton (k : ℕ) :
    ((p ^ k : ℕ) : ℤ_[p]) ∉ roundedSkeleton p k := by
  intro hx
  rcases hx with ⟨n, hn⟩
  have hcast : ((n : ℕ) : ℤ_[p]) = ((p ^ k : ℕ) : ℤ_[p]) := by simpa using hn.symm
  have hEq : (n : ℕ) = p ^ k := Nat.cast_injective hcast
  have : p ^ k < p ^ k := by simpa [hEq] using n.2
  exact Nat.lt_irrefl _ this

theorem gap_nonzero_at_finite_depth (k : ℕ) :
    ∃ S : DepthState p, (padicDepthNucleus p k).R S ≠ S := by
  refine ⟨({((p ^ k : ℕ) : ℤ_[p])} : Set ℤ_[p]), ?_⟩
  intro hEq
  have hsubset :
      (({((p ^ k : ℕ) : ℤ_[p])} : Set ℤ_[p]) : Set ℤ_[p]) ⊆ roundedSkeleton p k :=
    (depthRestrict_eq_self_iff (p := p) k ({((p ^ k : ℕ) : ℤ_[p])} : Set ℤ_[p])).1
      (by simpa [padicDepthNucleus_R_def] using hEq)
  have : ((p ^ k : ℕ) : ℤ_[p]) ∈ roundedSkeleton p k := hsubset (by simp)
  exact witness_outside_roundedSkeleton (p := p) k this

/--
As depth increases, the fixed-point family expands. This is dual to saying the
unresolved boundary gap decreases with more visible p-adic detail.
-/
theorem gap_monotone_decreasing {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) :
    fixedPointsAtDepth p k₁ ⊆ fixedPointsAtDepth p k₂ :=
  fixedPoints_monotone (p := p) h

end HeytingLean.PadicDecoupling.Nucleus
