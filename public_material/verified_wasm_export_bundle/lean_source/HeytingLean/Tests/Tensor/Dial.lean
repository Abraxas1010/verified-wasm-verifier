import HeytingLean.Computational.Tensor.Core
import HeytingLean.Computational.Tensor.Nucleus
import HeytingLean.Computational.Tensor.DialAdapter

/-
Compile-only smoke test for dial→temperature adapter.
-/

namespace HeytingLean
namespace Tests
namespace Tensor

open HeytingLean.Computational.Tensor

def N0 : TensorNucleus Nat :=
  { dim := 1
  , embed := fun n => EmbVec.ofList [Float.ofNat n]
  , core := fun v => v
  , temperature := 0.0 }

def r01 : TempRange := { minT := 0.0, maxT := 1.0 }
def r05 : TempRange := { minT := 0.1, maxT := 0.5 }

def Nlin (lvl : Nat) : TensorNucleus Nat :=
  withDialLevel N0 r01 lvl 10

def Neased (lvl : Nat) : TensorNucleus Nat :=
  withDialLevelEased N0 r05 2.0 lvl 10

end Tensor
end Tests
end HeytingLean

