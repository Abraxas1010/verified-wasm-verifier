import HeytingLean.Computational.Tensor.Core
import HeytingLean.Computational.Tensor.Algebra
import HeytingLean.Computational.Tensor.Nucleus

/-
Compile-only smoke test for the Tensor scaffold.
-/

namespace HeytingLean
namespace Tests
namespace Tensor

open HeytingLean.Computational.Tensor

def idCore : CoreTransform := fun v => v

def natEmbed (n : Nat) : EmbVec :=
  EmbVec.ofList [Float.ofNat n]

def NNat : TensorNucleus Nat :=
  { dim := 1, embed := natEmbed, core := idCore, temperature := 0.0 }

-- ensure functions are called so code is referenced
def demoVec : EmbVec := NNat.applyCore 7

-- small matvec demo: [[2,0],[0,3]] * [n,1]
def M2 : EmbMat := EmbMat.fromRows [[2.0, 0.0], [0.0, 3.0]]
def v2 (n : Nat) : EmbVec := EmbVec.ofList [Float.ofNat n, 1.0]
def mvOut (n : Nat) : EmbVec := matvec M2 (v2 n)
def linCore : CoreTransform := mkLinearCore M2
def mvOut2 (n : Nat) : EmbVec := linCore (v2 n)

end Tensor
end Tests
end HeytingLean
