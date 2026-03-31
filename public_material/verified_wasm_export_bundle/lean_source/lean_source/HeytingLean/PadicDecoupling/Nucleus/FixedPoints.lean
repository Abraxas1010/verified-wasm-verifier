import HeytingLean.PadicDecoupling.Nucleus.PadicRounding

noncomputable section

namespace HeytingLean.PadicDecoupling.Nucleus

open Set

variable (p : ℕ) [Fact p.Prime]

abbrev fixedPointsAtDepth (k : ℕ) : Set (DepthState p) :=
  (padicDepthNucleus p k).fixedPoints

theorem mem_fixedPointsAtDepth_iff {k : ℕ} {S : DepthState p} :
    S ∈ fixedPointsAtDepth p k ↔ asSet p S ⊆ roundedSkeleton p k := by
  show (padicDepthNucleus p k).R S = S ↔ asSet p S ⊆ roundedSkeleton p k
  rw [padicDepthNucleus_R_def]
  exact depthRestrict_eq_self_iff (p := p) k S

theorem fixedPoints_finite (k : ℕ) :
    (fixedPointsAtDepth p k).Finite := by
  classical
  let U := roundedSkeleton p k
  let f : fixedPointsAtDepth p k → Set U :=
    fun S x => x.1 ∈ asSet p S.1
  have hf : Function.Injective f := by
    intro S T hST
    apply Subtype.ext
    ext x
    constructor
    · intro hx
      have hSsub : asSet p S.1 ⊆ U := (mem_fixedPointsAtDepth_iff (p := p)).1 S.2
      have hxU : x ∈ U := hSsub hx
      have : (⟨x, hxU⟩ : U) ∈ f T := by
        rw [← hST]
        simpa [f] using hx
      simpa [f] using this
    · intro hx
      have hTsub : asSet p T.1 ⊆ U := (mem_fixedPointsAtDepth_iff (p := p)).1 T.2
      have hxU : x ∈ U := hTsub hx
      have : (⟨x, hxU⟩ : U) ∈ f S := by
        rw [hST]
        simpa [f] using hx
      simpa [f] using this
  haveI : Finite U := (roundedSkeleton_finite (p := p) k).to_subtype
  haveI : Finite (Set U) := inferInstance
  haveI : Finite (fixedPointsAtDepth p k) := Finite.of_injective f hf
  exact Set.toFinite _

theorem fixedPoints_monotone {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) :
    fixedPointsAtDepth p k₁ ⊆ fixedPointsAtDepth p k₂ := by
  intro S hS
  rw [mem_fixedPointsAtDepth_iff (p := p)] at hS ⊢
  intro x hx
  exact (roundedSkeleton_mono (p := p) h) (hS hx)

end HeytingLean.PadicDecoupling.Nucleus
