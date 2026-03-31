import HeytingLean.Computational.Tensor.Core
import HeytingLean.Computational.Tensor.Algebra
import HeytingLean.Computational.Tensor.Nucleus
import HeytingLean.Computational.Tensor.DialAdapter

namespace HeytingLean
namespace CLI

open HeytingLean.Computational.Tensor

def TensorDemo.run : IO Unit := do
  let M : EmbMat := EmbMat.fromRows [[2.0, 0.0], [0.0, 3.0]]
  let v : EmbVec := EmbVec.ofList [1.0, 1.0]
  let mv := matvec M v
  let N : TensorNucleus Nat :=
    { dim := 2
    , embed := fun n => EmbVec.ofList [Float.ofNat n, 1.0]
    , core := mkLinearCore M
    , temperature := 0.0 }
  let Nlin := withDialLevel N { minT := 0.0, maxT := 1.0 } 5 10
  let Nease := withDialLevelEased N { minT := 0.1, maxT := 0.5 } 2.0 5 10
  IO.println s!"Tensor demo: matvec [[2,0],[0,3]] * [1,1] = {mv.data}"
  IO.println s!"N temperature (linear): {Nlin.temperature}"
  IO.println s!"N temperature (eased) : {Nease.temperature}"

end CLI
end HeytingLean

def main : IO Unit :=
  HeytingLean.CLI.TensorDemo.run

