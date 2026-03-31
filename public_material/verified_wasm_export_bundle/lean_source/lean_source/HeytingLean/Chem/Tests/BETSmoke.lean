import HeytingLean.Chem.Theories.Adsorption.BET

/-!
# BET adsorption smoke tests
-/

namespace HeytingLean
namespace Chem
namespace Tests

open HeytingLean.Chem.Theories.Adsorption

-- Compile-only: ensures the linear-form theorem type-checks.
example {K : Type} [Field K]
    (x v_m C : K)
    (hx0 : x ≠ 0)
    (hv_m : v_m ≠ 0)
    (hC : C ≠ 0)
    (hx : (1 - x) ≠ 0) :
    x / (BET x v_m C * (1 - x))
      = 1 / (v_m * C) + (C - 1) / (v_m * C) * x := by
  simpa using bet_linear_form (x := x) (v_m := v_m) (C := C) hx0 hv_m hC hx

end Tests
end Chem
end HeytingLean
