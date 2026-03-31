import Mathlib.Tactic

/-!
# BET adsorption (algebraic layer)

We record the standard BET isotherm in a field `K`:

  v = v_m * C * x / ((1 - x) * (1 + (C - 1) * x))

where `x = P/P0` is the relative pressure, `v_m` is the monolayer capacity, and
`C` is the BET constant.

This module is intentionally algebraic/structural: it does not attempt to
formalize the kinetic assumptions of BET at M0. It provides the canonical
equation and a clean equivalence to the common linear form used in practice.
-/

namespace HeytingLean
namespace Chem
namespace Theories
namespace Adsorption

variable {K : Type} [Field K]

/-- BET isotherm (nonlinear form). -/
def BET (x v_m C : K) : K :=
  v_m * C * x / ((1 - x) * (1 + (C - 1) * x))

/-- The standard linear BET form derived from the nonlinear expression. -/
theorem bet_linear_form
    (x v_m C : K)
    (hx0 : x ≠ 0)
    (hv_m : v_m ≠ 0)
    (hC : C ≠ 0)
    (hx : (1 - x) ≠ 0) :
    x / (BET x v_m C * (1 - x))
      = 1 / (v_m * C) + (C - 1) / (v_m * C) * x := by
  unfold BET
  field_simp [hx0, hv_m, hC, hx]

end Adsorption
end Theories
end Chem
end HeytingLean
