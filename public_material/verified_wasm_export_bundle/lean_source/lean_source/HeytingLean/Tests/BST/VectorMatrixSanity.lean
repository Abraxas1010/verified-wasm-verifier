import HeytingLean.BST.Numbers

namespace HeytingLean.Tests.BST.VectorMatrixSanity

open HeytingLean.BST
open HeytingLean.BST.BoundedTranscendental

def negOne₁ : RealB 1 := ⟨0, by decide⟩
def zero₁ : RealB 1 := ⟨1, by decide⟩
def one₁ : RealB 1 := ⟨2, by decide⟩

lemma hk1 : 0 < 1 := by decide

def vOne : BVector 1 1 := fun _ => one₁
def vAlt : BVector 1 2 := fun i => if i.1 = 0 then one₁ else negOne₁

example : BVector.dot hk1 vAlt vAlt = 2 := by
  native_decide

example : boundedExp 0 5 = 1 := by
  native_decide

example : boundedSin 0 5 = 0 := by
  native_decide

example : boundedCos 0 5 = 1 := by
  native_decide

example : boundedSin 0 5 ^ 2 + boundedCos 0 5 ^ 2 = 1 := by
  native_decide

example : BMatrix.mulVecRound hk1 (BMatrix.identity 1 1) vOne = vOne := by
  exact BMatrix.identity_mulVec hk1 vOne

example : 0 ≤ BVector.dot hk1 vAlt vAlt := by
  exact BVector.dot_self_nonneg hk1 vAlt

example : BMatrix.isSymmetric (BMatrix.identity 1 2) := by
  exact BMatrix.isSymmetric_identity 1 2

end HeytingLean.Tests.BST.VectorMatrixSanity
