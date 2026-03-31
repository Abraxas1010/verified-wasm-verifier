import HeytingLean.Magma.Separation.MSS

namespace HeytingLean.Magma.Separation

open HeytingLean.Magma

variable {A : Type*} [MagmaticAtoms A] [u : MagmaticUniverse A] [PairEncoding A] [ProductEncoding A]
  [SeparationPresentation A]

def ImageClosed (X : Set (Set (Magma A))) : Prop :=
  ∀ ⦃S : Set (Magma A)⦄, S ∈ X → ∀ ⦃T : Set (Magma A)⦄, T ⊆ S → T ∈ X

def predecessorImage (u0 : Magma A) : Set (Set (Magma A)) :=
  { S | ∃ x : Magma A, x ∈ u0 ∧ S = { y : Magma A | y ≤ x } }

structure ReplacementCounterexample (u0 : Magma A) where
  witness : Set (Magma A)
  witness_mem : witness ∈ predecessorImage (A := A) u0
  smaller : Set (Magma A)
  smaller_subset : smaller ⊆ witness
  smaller_not_mem : smaller ∉ predecessorImage (A := A) u0

/-- The constructive witness is supplied by the ambient presentation: a specific
subfamily of a predecessor image that fails to stay inside the image family. -/
class ReplacementFailurePresentation (A : Type*) [MagmaticAtoms A] [MagmaticUniverse A]
    [PairEncoding A] [ProductEncoding A] [SeparationPresentation A] where
  replacement_counterexample :
    ∀ (u0 : Magma A), ReplacementCounterexample (A := A) u0

theorem replacement_fails [ReplacementFailurePresentation A] (u0 : Magma A) :
    ¬ ImageClosed (predecessorImage (A := A) u0) := by
  intro hClosed
  let c := ReplacementFailurePresentation.replacement_counterexample (A := A) u0
  exact c.smaller_not_mem (hClosed c.witness_mem c.smaller_subset)

def collateral_unavoidable_conjecture : Prop :=
  ∀ {a₀ a₁ : A} (_h : Incomparable a₀ a₁)
    (pair_def : Magma A → Magma A → Magma A),
      (∀ x y x' y', pair_def x y = pair_def x' y' → x = x' ∧ y = y') →
      ∀ x y, ∃ x' y' : Magma A, x' < x ∧ y' < y

end HeytingLean.Magma.Separation
