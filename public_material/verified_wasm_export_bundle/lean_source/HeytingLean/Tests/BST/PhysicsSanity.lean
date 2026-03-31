import HeytingLean.BST.Physics

namespace HeytingLean.Tests.BST.Physics

open HeytingLean.BST
open HeytingLean.BST.Analysis
open HeytingLean.BST.Physics

def zero₁ : RealB 1 := ⟨1, by decide⟩
def one₁ : RealB 1 := ⟨2, by decide⟩
lemma hk1 : 0 < 1 := by decide

def moving₁ : State 1 where
  pos := zero₁
  vel := one₁

example : eulerStep 1 hk1 zero₁ (fun _ => one₁) one₁ = one₁ := by
  native_decide

example : eulerSteps 1 hk1 zero₁ (fun _ => one₁) 3 one₁ = one₁ := by
  exact eulerSteps_zero_dt 1 hk1 (fun _ => one₁) 3 one₁

example : advance 1 hk1 one₁ zero₁ (rest 1) = rest 1 := by
  native_decide

example : advanceSteps 1 hk1 one₁ zero₁ 4 (rest 1) = rest 1 := by
  native_decide

example : kineticEnergy 1 hk1 (rest 1) = 0 := by
  exact kineticEnergy_rest 1 hk1

example : speedSquared 1 hk1 moving₁ = 1 := by
  native_decide

example : kineticEnergy 1 hk1 moving₁ = (1 : Rat) / 2 := by
  native_decide

example :
    |RealB.toRat hk1 (eulerSteps 1 hk1 zero₁ (fun _ => zero₁) 3 zero₁) -
        eulerShadow 1 hk1 zero₁ (fun _ => zero₁) 3 zero₁| ≤
      ((2 * 3 : ℕ) : Rat) * RealB.halfStep 1 := by
  exact eulerSteps_shadow_error_le 1 hk1 zero₁ (fun _ => zero₁) 3 zero₁
    (by
      intro m
      simpa using
        (show |RealB.toRat hk1 zero₁ * RealB.toRat hk1 zero₁| ≤ (1 : Rat) by
          native_decide))
    (by
      intro m
      have hstep : eulerSteps 1 hk1 zero₁ (fun _ => zero₁) m zero₁ = zero₁ := by
        simpa [zero₁] using eulerSteps_zero_dt 1 hk1 (fun _ => zero₁) m zero₁
      simpa [hstep] using
        (show |RealB.toRat hk1 zero₁ + RealB.toRat hk1 (RealB.mul hk1 zero₁ zero₁)| ≤ (1 : Rat) by
          native_decide))

end HeytingLean.Tests.BST.Physics
