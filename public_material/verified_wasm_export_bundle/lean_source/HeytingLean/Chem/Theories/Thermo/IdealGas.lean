import Mathlib.Tactic

/-!
# Ideal gas law (algebraic layer)

This module records the ideal gas law as a simple algebraic relation and derives Boyle's law as a
direct consequence when temperature and amount are held fixed.

We keep this as "phenomenology": it is a reusable upper layer that does not depend on the QED
foundations being complete.
-/

namespace HeytingLean
namespace Chem
namespace Theories
namespace Thermo

/-- Ideal gas parameters: the gas constant `R`. -/
structure IdealGasParams (K : Type) [Field K] where
  R : K

/-- The ideal gas law equation `P * V = n * R * T`. -/
def IdealGasLaw {K : Type} [Field K] (P V n T : K) (params : IdealGasParams K) : Prop :=
  P * V = n * params.R * T

/-- Boyle's law: if `n`, `T` and `R` are fixed, then `P*V` is constant. -/
theorem boylesLaw
    {K : Type} [Field K]
    (params : IdealGasParams K)
    (n T : K)
    (P1 V1 P2 V2 : K)
    (h1 : IdealGasLaw P1 V1 n T params)
    (h2 : IdealGasLaw P2 V2 n T params) :
    P1 * V1 = P2 * V2 := by
  have h1' : P1 * V1 = n * params.R * T := by
    simpa [IdealGasLaw] using h1
  have h2' : P2 * V2 = n * params.R * T := by
    simpa [IdealGasLaw] using h2
  exact h1'.trans h2'.symm

end Thermo
end Theories
end Chem
end HeytingLean
