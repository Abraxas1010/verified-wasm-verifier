import HeytingLean.BST.Analysis

namespace HeytingLean.Tests.BST.Analysis

open HeytingLean.BST
open HeytingLean.BST.Analysis

def zero₁ : RealB 1 := ⟨1, by decide⟩
def one₁ : RealB 1 := ⟨2, by decide⟩
lemma hk1 : 0 < 1 := by decide

example :
    centralDiff 1 hk1 one₁
      (square 1 hk1) zero₁ = 0 := by
  native_decide

example :
    riemannSum 1 hk1 1 [zero₁, one₁] (square 1 hk1) = 1 := by
  native_decide

example : centralDiff 1 hk1 one₁ (fun _ => (5 : Rat)) zero₁ = 0 := by
  exact centralDiff_const 1 hk1 one₁ zero₁ 5

example : riemannSum 1 hk1 1 [] (square 1 hk1) = 0 := by
  exact riemannSum_nil 1 hk1 1 (square 1 hk1)

example :
    riemannSum 1 hk1 1 [zero₁, one₁]
      (fun x => square 1 hk1 x + 1) =
      riemannSum 1 hk1 1 [zero₁, one₁] (square 1 hk1) +
        riemannSum 1 hk1 1 [zero₁, one₁] (fun _ => (1 : Rat)) := by
  exact riemannSum_add 1 hk1 1 [zero₁, one₁]
    (square 1 hk1) (fun _ => (1 : Rat))

end HeytingLean.Tests.BST.Analysis
