import HeytingLean.BST.Numbers

namespace HeytingLean.Tests.BST.Number

open HeytingLean.BST

example : (NatB.checkedAdd (k := 5) ⟨2, by decide⟩ ⟨3, by decide⟩).isSome = true := by
  decide

example : (IntB.checkedAdd (k := 5) ⟨2, by decide⟩ ⟨-3, by decide⟩).isSome = true := by
  decide

example : (RatB.ofRat? 6 (((3 : Rat) / 2))).isSome = true := by
  native_decide

def zero₁ : RealB 1 := ⟨1, by decide⟩
def negOne₁ : RealB 1 := ⟨0, by decide⟩
def one₁ : RealB 1 := ⟨2, by decide⟩
lemma hk1 : 0 < 1 := by decide

example : RealB.toRat (k := 1) hk1 zero₁ = 0 := by
  native_decide

example : RealB.toRat (k := 1) hk1 one₁ = 1 := by
  native_decide

example : RealB.approxEq (k := 1) hk1 0 one₁ one₁ := by
  unfold RealB.approxEq
  norm_num [RealB.toRat, RealB.toInt, RealRadius, one₁, hk1]

example : RealB.default 1 = zero₁ := by
  rfl

example : RealB.default 1 ∈ RealB.candidates 1 := by
  exact RealB.default_mem_candidates 1

example : RealB.round (k := 1) hk1 (RealB.toRat (k := 1) hk1 one₁) ∈ RealB.candidates 1 := by
  exact RealB.round_mem_candidates (k := 1) hk1
    (RealB.toRat (k := 1) hk1 one₁)

example :
    RealB.distance (k := 1) hk1
      (RealB.round (k := 1) hk1 (RealB.toRat (k := 1) hk1 one₁))
      (RealB.toRat (k := 1) hk1 one₁) = 0 := by
  simpa using RealB.distance_round_self_eq_zero (k := 1) hk1 one₁

example :
    RealB.distance (k := 1) hk1 (RealB.round (k := 1) hk1 ((1 : Rat) / 2)) ((1 : Rat) / 2) ≤
      RealB.halfStep 1 := by
  exact RealB.distance_round_le_halfStep_of_abs_le_one (k := 1) hk1 (by norm_num)

example : RealB.approxEq (k := 1) hk1 1 negOne₁ zero₁ := by
  unfold RealB.approxEq
  native_decide

example : RealB.approxEq (k := 1) hk1 1 zero₁ one₁ := by
  unfold RealB.approxEq
  native_decide

example : RealB.approxEq (k := 1) hk1 ((1 : Rat) + 1) negOne₁ one₁ := by
  exact
    (RealB.approxEq_triangle (k := 1) hk1 1 1 negOne₁ zero₁ one₁
      (by
        unfold RealB.approxEq
        native_decide)
      (by
        unfold RealB.approxEq
        native_decide))

end HeytingLean.Tests.BST.Number
