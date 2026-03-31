import HeytingLean.Moonshine.VOA.Basic

set_option autoImplicit false

noncomputable section

open scoped VertexOperator

namespace HeytingLean.Moonshine.VOA

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- Mode-by-mode commutativity for two vertex operators. -/
def ModesCommute (A B : VertexOperator ℂ V) (m n : ℤ) : Prop :=
  (A[[m]]).comp (B[[n]]) = (B[[n]]).comp (A[[m]])

/-- Pairwise locality packaged as eventual mode commutation. -/
def PairwiseLocal (A : VOAData) : Prop :=
  ∀ a b : A.V, ∃ N : ℤ, ∀ m n : ℤ, N ≤ m + n → ModesCommute (A.Y a) (A.Y b) m n

lemma scalar_modes_commute (a b : ℂ) (m n : ℤ) :
    ModesCommute (scalarField a) (scalarField b) m n := by
  rw [ModesCommute, scalarField_mode_eq, scalarField_mode_eq]
  by_cases hm : m = 0
  · by_cases hn : n = 0
    · subst hm
      subst hn
      apply LinearMap.ext
      intro x
      simp [scalarMode, mul_left_comm]
    · simp [hm, hn]
  · by_cases hn : n = 0
    · simp [hm, hn]
    · simp [hm, hn]

theorem scalarVOA_pairwiseLocal : PairwiseLocal scalarVOA := by
  intro a b
  refine ⟨0, ?_⟩
  intro m n _h
  exact scalar_modes_commute a b m n

end HeytingLean.Moonshine.VOA
