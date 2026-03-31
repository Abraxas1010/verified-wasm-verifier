import Mathlib.Logic.Relation
import Mathlib.Data.Set.Lattice

open scoped Classical

namespace HeytingLean.LoF.Lens.Rewriting

variable {τ : Type _} (step : τ → τ → Prop)

/-- Downward interior: keep terms whose every ancestor (by `step*`) lies in `X`. -/
def I (X : Set τ) : Set τ :=
  { t | ∀ u, Relation.ReflTransGen step u t → u ∈ X }

namespace I

variable {step} (X Y : Set τ)

@[simp] lemma mem_iff {t : τ} : t ∈ I (step := step) X ↔ ∀ u, Relation.ReflTransGen step u t → u ∈ X := Iff.rfl

lemma monotone (hXY : X ⊆ Y) : I (step := step) X ⊆ I (step := step) Y := by
  intro t ht u hu; exact hXY ((mem_iff (step := step) (X := X)).mp ht u hu)

lemma idempotent : I (step := step) (I (step := step) X) = I (step := step) X := by
  apply Set.Subset.antisymm
  · intro t ht u hu
    have huIX : u ∈ I (step := step) X := (mem_iff (step := step) (X := I (step := step) X)).mp ht u hu
    exact (mem_iff (step := step) (X := X)).mp huIX u (Relation.ReflTransGen.refl)
  · intro t ht u hu v hv
    exact (mem_iff (step := step) (X := X)).mp ht v (Relation.ReflTransGen.trans hv hu)

lemma inf_preserving : I (step := step) (X ∩ Y) = I (step := step) X ∩ I (step := step) Y := by
  apply Set.ext
  intro t
  constructor
  · intro ht
    refine And.intro ?_ ?_
    · intro u hu
      exact ((mem_iff (step := step) (X := X ∩ Y)).mp ht u hu).1
    · intro u hu
      exact ((mem_iff (step := step) (X := X ∩ Y)).mp ht u hu).2
  · intro ht
    rcases ht with ⟨hX, hY⟩
    exact (mem_iff (step := step) (X := X ∩ Y)).mpr (fun u hu =>
      And.intro (hX u hu) (hY u hu))

end I

end HeytingLean.LoF.Lens.Rewriting
