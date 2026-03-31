import HeytingLean.Physics.String.Spec.QSeriesN
import HeytingLean.Physics.String.Spec.QSeriesNProps

/-!
Compile-only: proof-friendly QSeriesN nonnegativity.
-/

namespace HeytingLean
namespace Tests
namespace String
namespace Spec

open HeytingLean.Physics.String.Spec

def ws : List Nat := [0,1,1,2,0]
def qn : QSeriesN := QSeriesN.fromWeights ws

/-- All coefficients of `qn` are nonnegative when viewed in ℤ. -/
theorem qn_coeff_nonneg (i : Nat) :
    0 ≤ (QSeriesN.coeffAt qn i : Int) :=
  fromWeights_nonneg ws i

end Spec
end String
end Tests
end HeytingLean
