import HeytingLean.Moonshine.Monster.BasicLemmas
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Positivity

set_option autoImplicit false

namespace HeytingLean.Moonshine

/-- A convenience lemma: `monsterOrder ≠ 0`. -/
lemma monsterOrder_ne_zero : monsterOrder ≠ 0 := by
  exact (Nat.ne_of_gt monsterOrder_pos)

/-- `monsterOrder` is greater than 1 (so any group with this cardinality is nontrivial). -/
lemma monsterOrder_one_lt : 1 < monsterOrder := by
  -- `2^46 > 1`, and `monsterOrder` is a positive multiple of `2^46`.
  have h2 : 1 < (2 : Nat) ^ 46 := by
    exact Nat.one_lt_pow (by decide) Nat.one_lt_two
  have hle : (2 : Nat) ^ 46 ≤ monsterOrder := by
    dsimp [monsterOrder]
    -- Avoid associativity rewriting by growing the product factor-by-factor
    -- in the same (left-associated) shape as the definition.
    have h3  : 0 < (3 : Nat) ^ 20 := by positivity
    have h5  : 0 < (5 : Nat) ^ 9  := by positivity
    have h7  : 0 < (7 : Nat) ^ 6  := by positivity
    have h11 : 0 < (11 : Nat) ^ 2 := by positivity
    have h13 : 0 < (13 : Nat) ^ 3 := by positivity
    have h17 : 0 < (17 : Nat) := by positivity
    have h19 : 0 < (19 : Nat) := by positivity
    have h23 : 0 < (23 : Nat) := by positivity
    have h29 : 0 < (29 : Nat) := by positivity
    have h31 : 0 < (31 : Nat) := by positivity
    have h41 : 0 < (41 : Nat) := by positivity
    have h47 : 0 < (47 : Nat) := by positivity
    have h59 : 0 < (59 : Nat) := by positivity
    have h71 : 0 < (71 : Nat) := by positivity

    -- Chain `x ≤ x * k` repeatedly.
    refine le_trans (Nat.le_mul_of_pos_right ((2 : Nat) ^ 46) h3) ?_
    refine le_trans (Nat.le_mul_of_pos_right ((2 : Nat) ^ 46 * (3 : Nat) ^ 20) h5) ?_
    refine le_trans (Nat.le_mul_of_pos_right
      ((2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9) h7) ?_
    refine le_trans (Nat.le_mul_of_pos_right
      ((2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6) h11) ?_
    refine le_trans (Nat.le_mul_of_pos_right
      ((2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2) h13) ?_
    refine le_trans (Nat.le_mul_of_pos_right
      ((2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3) h17) ?_
    refine le_trans (Nat.le_mul_of_pos_right
      ((2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17) h19) ?_
    refine le_trans (Nat.le_mul_of_pos_right
      ((2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19) h23) ?_
    refine le_trans (Nat.le_mul_of_pos_right
      ((2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23) h29) ?_
    refine le_trans (Nat.le_mul_of_pos_right
      ((2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 * 29) h31) ?_
    refine le_trans (Nat.le_mul_of_pos_right
      ((2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 * 29 * 31) h41) ?_
    refine le_trans (Nat.le_mul_of_pos_right
      ((2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 * 29 * 31 * 41) h47) ?_
    refine le_trans (Nat.le_mul_of_pos_right
      ((2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 * 29 * 31 * 41 * 47) h59) ?_
    refine le_trans (Nat.le_mul_of_pos_right
      ((2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 * 29 * 31 * 41 * 47 * 59) h71) ?_
    exact le_rfl
  exact lt_of_lt_of_le h2 hle

namespace MonsterSpec

variable (S : MonsterSpec)

lemma natCard : Nat.card S.M = monsterOrder := by
  classical
  -- Convenient bridge: many group-theory lemmas are stated using `Nat.card`.
  simp [Nat.card_eq_fintype_card, S.card_eq]

lemma one_lt_card : 1 < Fintype.card S.M := by
  simp [S.card_eq, monsterOrder_one_lt]

instance : Nontrivial S.M :=
  (Fintype.one_lt_card_iff_nontrivial).1 (S.one_lt_card)

end MonsterSpec

end HeytingLean.Moonshine
