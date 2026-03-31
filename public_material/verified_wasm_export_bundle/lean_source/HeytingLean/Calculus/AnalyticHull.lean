import Mathlib.Data.Set.Lattice

/-!
Analytic hull on sets of real functions via a Moore family (intersection
of closed supersets under a minimal closedness predicate: pointwise equality).
This is pure set/lattice reasoning; no heavy analysis is imported.
-/

namespace HeytingLean
namespace Calculus

open Set

/-- Minimal closedness notion: closed under pointwise equality. -/
def EqClosed (S : Set (ℝ → ℝ)) : Prop :=
  ∀ ⦃f g⦄, f ∈ S → (∀ x, f x = g x) → g ∈ S

lemma EqClosed_sInter {𝒞 : Set (Set (ℝ → ℝ))}
    (h : ∀ C ∈ 𝒞, EqClosed C) : EqClosed (⋂₀ 𝒞) := by
  intro f g hf hfg
  refine mem_sInter.mpr ?all
  intro C hC
  have hfAll := mem_sInter.mp hf
  have hfC : f ∈ C := hfAll C hC
  exact (h C hC) hfC hfg

/-- Analytic hull as the intersection of all EqClosed supersets of `A`. -/
def analyticHull (A : Set (ℝ → ℝ)) : Set (ℝ → ℝ) :=
  ⋂₀ { C | EqClosed C ∧ A ⊆ C }

lemma analyticHull_extensive (A : Set (ℝ → ℝ)) : A ⊆ analyticHull A := by
  intro f hf
  refine mem_sInter.mpr ?all
  intro C hC; exact hC.2 hf

lemma analyticHull_eqClosed (A : Set (ℝ → ℝ)) : EqClosed (analyticHull A) := by
  refine EqClosed_sInter (fun C hC => hC.1)

lemma analyticHull_idem (A : Set (ℝ → ℝ)) :
    analyticHull (analyticHull A) = analyticHull A := by
  apply le_antisymm
  · -- hull(hull A) ⊆ hull A
    intro f hf
    have hfAll := mem_sInter.mp hf
    exact hfAll (analyticHull A)
      ⟨analyticHull_eqClosed A, by intro x hx; exact hx⟩
  · -- hull A ⊆ hull(hull A)
    intro f hf
    refine mem_sInter.mpr ?all
    intro C hC
    -- From A ⊆ hull A and hull A ⊆ C we get A ⊆ C
    have hAincl : A ⊆ C := by
      intro x hxA; exact hC.2 (analyticHull_extensive A hxA)
    exact (mem_sInter.mp hf) C ⟨hC.1, hAincl⟩

lemma analyticHull_monotone {A B : Set (ℝ → ℝ)}
    (hAB : A ⊆ B) : analyticHull A ⊆ analyticHull B := by
  intro f hf
  -- membership in hull B means: f lies in every EqClosed C with B ⊆ C
  refine mem_sInter.mpr ?all
  intro C hC
  -- from A ⊆ B and B ⊆ C we have A ⊆ C, so hf gives f ∈ C
  have hAC : A ⊆ C := by
    intro x hxA; exact hC.2 (hAB hxA)
  exact (mem_sInter.mp hf) C ⟨hC.1, hAC⟩

-- Note: additional properties (like meet preservation) depend on the chosen
-- closed-family. With `EqClosed` alone, we refrain from asserting meet laws.

end Calculus
end HeytingLean
