import HeytingLean.BST.Analysis

namespace HeytingLean.Tests.BST.AnalysisToolkitSanity

open HeytingLean.BST
open HeytingLean.BST.Analysis

def zero₁ : RealB 1 := ⟨1, by decide⟩
def one₁ : RealB 1 := ⟨2, by decide⟩

lemma hk1 : 0 < 1 := by decide
lemma hN3 : 0 < 3 := by decide

def zeroVec : BVector 1 1 := fun _ => zero₁
def oneVec : BVector 1 1 := fun _ => one₁
def zeroField : BVector 1 1 → BVector 1 1 := fun _ => zeroVec

example :
    symplecticEuler hk1 zeroField zeroField (RealB.default 1) oneVec zeroVec = (oneVec, zeroVec) := by
  exact symplecticEuler_zero_dt hk1 zeroField zeroField oneVec zeroVec

example :
    stoermerVerlet hk1 zeroField zeroField (RealB.default 1) oneVec zeroVec = (oneVec, zeroVec) := by
  exact stoermerVerlet_zero_dt hk1 zeroField zeroField oneVec zeroVec

example : BMatrix.isSymmetric (laplacian1D 1 3 hk1 hN3 one₁) := by
  exact laplacian1D_symmetric 1 3 hk1 hN3 one₁

example :
    BMatrix.mulVec hk1 (laplacian1D 1 3 hk1 hN3 one₁) (fun _ => one₁) = fun _ => (0 : Rat) := by
  exact laplacian1D_constant_kernel 1 3 hk1 hN3 one₁ one₁

example : finiteDelta hk1 one₁ zero₁ = 1 := by
  native_decide

example : finiteDelta hk1 one₁ one₁ = 0 := by
  native_decide

end HeytingLean.Tests.BST.AnalysisToolkitSanity
