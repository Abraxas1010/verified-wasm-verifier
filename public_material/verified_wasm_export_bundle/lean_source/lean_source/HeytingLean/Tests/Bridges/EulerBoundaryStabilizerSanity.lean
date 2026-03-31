import HeytingLean.Bridges.EulerBoundaryStabilizer

/-!
# Tests.Bridges.EulerBoundaryStabilizerSanity

Compile-only checks for Euler-boundary -> stabilizer-code wrappers.
-/

namespace HeytingLean
namespace Tests
namespace Bridges

open HeytingLean.Bridges

universe u

section

variable {α : Type u} [HeytingLean.LoF.PrimaryAlgebra α]

example (R : HeytingLean.LoF.Reentry α) :
    let M : Graph.Model α := ⟨R⟩
    M.encode M.R.eulerBoundary ∈
      (EulerBoundaryStabilizer.graphEulerBoundaryCode M).codeSpace := by
  intro M
  simpa using EulerBoundaryStabilizer.graph_encode_eulerBoundary_mem_codeSpace (M := M)

example (R : HeytingLean.LoF.Reentry α) :
    let M : Clifford.Model α := ⟨R⟩
    M.encode M.R.eulerBoundary ∈
      (EulerBoundaryStabilizer.cliffordEulerBoundaryCode M).codeSpace := by
  intro M
  simpa using EulerBoundaryStabilizer.clifford_encode_eulerBoundary_mem_codeSpace (M := M)

end

end Bridges
end Tests
end HeytingLean
