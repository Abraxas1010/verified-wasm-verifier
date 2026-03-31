import HeytingLean.Matula.Compute.Encoder
import HeytingLean.Matula.Compute.Decoder
import HeytingLean.Matula.Core.Bijection

namespace HeytingLean
namespace Matula

example : nthPrime 1 = 2 := by
  native_decide

example : nthPrime 2 = 3 := by
  native_decide

example : nthPrime 3 = 5 := by
  native_decide

example : primeIndex 2 = 1 := by
  native_decide

example : primeIndex 3 = 2 := by
  native_decide

example : primeIndex 5 = 3 := by
  native_decide

example : (List.range 24).all (fun k => primeIndex (nthPrime (k + 1)) = k + 1) = true := by
  native_decide

example : matulaEncode RTree.leaf = 1 := by
  simp [matulaEncode, matula]

example : matulaEncode (.node [.leaf]) = 2 := by
  native_decide

example : matulaEncode (matulaDecode 2) = 2 := by
  native_decide

example : matulaEncode (.node []) = 1 := by
  native_decide

example : matulaEncode (matulaDecode (matulaEncode (.node []))) = 1 := by
  native_decide

end Matula
end HeytingLean
