import HeytingLean.Moonshine.Monster.OrderFacts
import Mathlib.GroupTheory.ClassEquation

set_option autoImplicit false

namespace HeytingLean.Moonshine

open ConjClasses

namespace MonsterSpec

variable (S : MonsterSpec)

/-- The center has `Nat.card = 1` (since it is trivial by spec). -/
lemma natCard_center : Nat.card (Subgroup.center S.M) = 1 := by
  classical
  -- Rewrite `center` to `⊥`, then use `Subgroup.card_bot`.
  rw [S.center_trivial]
  exact Subgroup.card_bot (G := S.M)

/-- The class equation specialized to a `MonsterSpec`. -/
lemma nat_card_center_add_sum_card_noncenter_eq_card :
    Nat.card (Subgroup.center S.M) + ∑ᶠ x ∈ noncenter S.M, Nat.card x.carrier =
      Nat.card S.M := by
  classical
  -- This is the standard class equation from mathlib.
  exact Group.nat_card_center_add_sum_card_noncenter_eq_card (G := S.M)

/-- The class equation with the center rewritten as `1` using `center_trivial`. -/
lemma one_add_sum_card_noncenter_eq_natCard :
    1 + ∑ᶠ x ∈ noncenter S.M, Nat.card x.carrier = Nat.card S.M := by
  classical
  have h := S.nat_card_center_add_sum_card_noncenter_eq_card
  -- Avoid `simp` rewriting `Nat.card` into `Fintype.card`; just rewrite the single `1`.
  rw [← S.natCard_center]  -- rewrites `1` to `Nat.card (Subgroup.center S.M)`
  exact h

end MonsterSpec

end HeytingLean.Moonshine
