import HeytingLean.Physics.String.Spec.QSeriesN
import HeytingLean.Physics.String.Spec.QSeriesNProps
import HeytingLean.Physics.String.Spec.OrbitClosure

/-!
Compile-only checks for the closure operator on `QSeriesN` in a small example.
-/

namespace HeytingLean
namespace Tests
namespace String
namespace Spec

open HeytingLean.Physics.String.Spec

def qA : QSeriesN := QSeriesN.fromWeights [0,1,2]

/-- Coefficients of `qA` are nonnegative when viewed in ℤ. -/
theorem qA_coeff_nonneg (i : Nat) :
    0 ≤ (QSeriesN.coeffAt qA i : Int) :=
  fromWeights_nonneg [0,1,2] i

/-- The closure operator is extensive on `qA`. -/
theorem qA_cl_extensive :
    lePointwise qA (cl qA) :=
  cl_extensive qA

/-- The closure operator is idempotent on `qA`. -/
theorem qA_cl_idem :
    cl (cl qA) = cl qA :=
  cl_idem qA

/-- The closure operator is monotone with respect to pointwise ≤, here
instantiated with reflexivity. -/
theorem qA_cl_mono :
    lePointwise (cl qA) (cl qA) :=
  cl_mono (lePointwise_refl qA)

end Spec
end String
end Tests
end HeytingLean
