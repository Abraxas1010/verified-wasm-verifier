import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Sites.Grothendieck

/-!
# Bool (M,R) configuration site (scoped work): a reachability category and dense topology

This module builds a small, **semantics-driven** MR-side category intended to align with the
SKY multiway reachability site at the *shape* level.

We fix a Boolean transition

`R : Bool → Bool → Bool`

and consider configurations `(state, remainingWord)`. A configuration `c₁` reaches `c₂` iff `c₂` is
obtained by consuming a prefix of `c₁.word`, updating the state by iterating `R` along that prefix.

We package this reachability as a preorder category and equip it with the **dense Grothendieck
topology** (`GrothendieckTopology.dense`), matching the SKY `StepsCat` dense site shape.

Objectivity boundary:
- this is a Bool-level (finite alphabet) semantics layer; it does not claim a general `(M,R)`→SKY site functor.
- the topology used here is the standard dense topology on the reachability category.
- the MR→SKY bridge is implemented separately in `ConfigSiteSKYBridge.lean`.
-/

namespace HeytingLean
namespace LoF
namespace MRSystems

namespace BoolConfig

/-! ## Deterministic fold semantics on words -/

/-- Deterministic fold of a Boolean transition `R` along a finite input word. -/
def run (R : Bool → Bool → Bool) : Bool → List Bool → Bool
  | b, [] => b
  | b, a :: w => run R (R b a) w

theorem run_append (R : Bool → Bool → Bool) (b : Bool) (w₁ w₂ : List Bool) :
    run R b (w₁ ++ w₂) = run R (run R b w₁) w₂ := by
  induction w₁ generalizing b with
  | nil =>
      simp [run]
  | cons a w₁ ih =>
      simp [run, ih]

/-! ## Configurations and reachability -/

/-- MR configurations for a fixed Boolean transition `R`:
current state `state` and remaining input word `word`. -/
structure Config (R : Bool → Bool → Bool) where
  state : Bool
  word : List Bool

namespace Config

variable {R : Bool → Bool → Bool}

/-- Reachability: `c₁ ≤ c₂` iff `c₂` is obtained by consuming some prefix of `c₁.word`. -/
def Reachable (c₁ c₂ : Config R) : Prop :=
  ∃ w : List Bool, c₁.word = w ++ c₂.word ∧ c₂.state = run R c₁.state w

theorem reachable_refl (c : Config R) : Reachable (R := R) c c := by
  refine ⟨[], ?_, ?_⟩ <;> simp [run]

theorem reachable_trans {c₁ c₂ c₃ : Config R} :
    Reachable (R := R) c₁ c₂ → Reachable (R := R) c₂ c₃ → Reachable (R := R) c₁ c₃ := by
  rintro ⟨w₁₂, hw₁₂, hs₂⟩ ⟨w₂₃, hw₂₃, hs₃⟩
  refine ⟨w₁₂ ++ w₂₃, ?_, ?_⟩
  · -- word bookkeeping
    -- `c₁.word = w₁₂ ++ c₂.word = w₁₂ ++ (w₂₃ ++ c₃.word) = (w₁₂ ++ w₂₃) ++ c₃.word`.
    simp [hw₁₂, hw₂₃, List.append_assoc]
  · -- state bookkeeping (fold associativity)
    calc
      c₃.state = run R c₂.state w₂₃ := hs₃
      _ = run R (run R c₁.state w₁₂) w₂₃ := by simp [hs₂]
      _ = run R c₁.state (w₁₂ ++ w₂₃) := by
        symm
        simpa using (run_append (R := R) (b := c₁.state) (w₁ := w₁₂) (w₂ := w₂₃))

end Config

/-! ## Category + dense topology -/

open CategoryTheory

instance (R : Bool → Bool → Bool) : Preorder (Config R) where
  le := Config.Reachable (R := R)
  le_refl := Config.reachable_refl (R := R)
  le_trans _ _ _ := Config.reachable_trans (R := R)

/-- The dense Grothendieck topology on the Boolean MR configuration reachability category. -/
def denseTopology (R : Bool → Bool → Bool) : GrothendieckTopology (Config R) :=
  GrothendieckTopology.dense

end BoolConfig

end MRSystems
end LoF
end HeytingLean
