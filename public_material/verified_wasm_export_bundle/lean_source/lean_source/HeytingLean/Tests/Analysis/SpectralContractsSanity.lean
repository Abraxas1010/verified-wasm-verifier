import HeytingLean.Analysis.Graph.SpectralContracts
import HeytingLean.Analysis.ContinualMetricsContract

namespace HeytingLean
namespace Tests
namespace Analysis

open HeytingLean.Analysis
open HeytingLean.Analysis.Graph
open HeytingLean.Analysis.Graph.NormalizedLaplacianContract
open HeytingLean.Analysis.ContinualMetricsContract

/-! Compile-time sanity checks for CL spectral/metric contracts. -/

namespace SpectralContractsDemo

private def identityContract (n : Nat) : NormalizedLaplacianContract n where
  L := 1
  symm := by
    exact (Matrix.isSymm_one : (1 : Matrix (Fin n) (Fin n) ℝ).IsSymm)
  psd := by
    intro x
    simpa [dotProduct] using (Finset.sum_nonneg fun i _ => mul_self_nonneg (x i))
  lambda2 := 1
  lambda2_nonneg := by norm_num
  connected := True
  connected_iff_lambda2_pos := by norm_num

example (n : Nat) (x : Fin n → ℝ) :
    0 ≤ x ⬝ᵥ ((identityContract n).L.mulVec x) := by
  exact (identityContract n).normalized_laplacian_psd x

example (n : Nat) : 0 ≤ (identityContract n).lambda2 := by
  exact (identityContract n).lambda2_nonnegative

example (n : Nat) : (identityContract n).connected := by
  have hpos : (0 : ℝ) < (identityContract n).lambda2 := by
    simp [identityContract]
  exact (identityContract n).connected_of_lambda2_pos hpos

end SpectralContractsDemo

namespace ContinualContractsDemo

private def toyContract : ContinualMetricsContract 2 where
  accuracy := fun _ _ => 1
  accuracy_bounded := by
    intro _ _
    constructor <;> norm_num
  peak := fun _ => 1
  final := fun _ => 0
  peak_spec := by
    intro _
    constructor <;> norm_num
  final_spec := by
    intro _
    norm_num

example (j : Fin 2) : toyContract.forgettingAt j = (1 : ℝ) := by
  norm_num [ContinualMetricsContract.forgettingAt, toyContract]

example (j : Fin 2) : 0 ≤ toyContract.forgettingAt j := by
  exact toyContract.forgetting_metric_nonneg j

example : 0 ≤ toyContract.totalForgetting := by
  exact toyContract.total_forgetting_nonneg

end ContinualContractsDemo

end Analysis
end Tests
end HeytingLean
