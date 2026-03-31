import HeytingLean.Physics.String.Spec.QSeriesN

/-!
Simple properties of `QSeriesN` used for small formal checks.
-/ 

namespace HeytingLean
namespace Physics
namespace String
namespace Spec

open QSeriesN

theorem coeffAt_nonneg (q : QSeriesN) (i : Nat) :
    0 ≤ (coeffAt q i : Int) := by
  simpa [coeffAt]

theorem fromWeights_nonneg (ws : List Nat) (i : Nat) :
    0 ≤ (coeffAt (fromWeights ws) i : Int) := by
  simpa [fromWeights, coeffAt]

end Spec
end String
end Physics
end HeytingLean
