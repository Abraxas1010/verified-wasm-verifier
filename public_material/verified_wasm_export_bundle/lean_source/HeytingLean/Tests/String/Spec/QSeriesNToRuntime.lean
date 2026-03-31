import HeytingLean.Physics.String.Spec.QSeriesN
import HeytingLean.Physics.String.Spec.QSeriesNToRuntime

/-
Compile-only: exercise the `QSeriesN.toRuntime` bridge.

This keeps the spec/runtime link under strict builds without
introducing any additional theorems.
-/

namespace HeytingLean
namespace Tests
namespace String
namespace Spec

open HeytingLean.Physics.String.Spec

def demo : IO Unit := do
  let ws : List Nat := [0, 1, 1, 2]
  let qn : QSeriesN := QSeriesN.fromWeights ws
  let qr := QSeriesN.toRuntime qn
  -- Print the spec coefficients and their runtime Float cast
  IO.println s!"QSeriesN coeffs={qn.coeffs}"
  IO.println s!"QSeries runtime coeffs={qr.coeffs}"

end Spec
end String
end Tests
end HeytingLean
