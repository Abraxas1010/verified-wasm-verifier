import HeytingLean.Quantum.TWA.Core

namespace HeytingLean
namespace Tests
namespace Quantum
namespace TWA

open HeytingLean.Quantum.TWA

/-! Quick compile-time regressions for Phase 1 (TWA core). -/

example (b v : SpinVector) : SpinVector.tangentToSphere v (SpinVector.hamiltonianVF b v) := by
  simpa using SpinVector.hamiltonianVF_tangent (b := b) (v := v)

example : (LindbladSpec.dim ⟨1, 0, (fun _ => 0), (fun j => nomatch j), 0, by
    simpa using (HeytingLean.Quantum.PosSemidef.zero (ι := Fin 0))⟩) = 3 := by
  simp [LindbladSpec.dim]

end TWA
end Quantum
end Tests
end HeytingLean

