import HeytingLean.Chem.Theories.Adsorption.Langmuir
import HeytingLean.Chem.Theories.Thermo.IdealGas

/-!
# Phenomenology smoke tests

Compile-only checks that the phenomenological chemistry theory layer is usable.
-/

namespace HeytingLean
namespace Chem
namespace Tests

namespace Adsorption

open HeytingLean.Chem.Theories.Adsorption

example (P k_ad k_d A S : ℚ)
    (hreaction : k_ad * P * S = k_d * A)
    (hS : S ≠ 0)
    (hk_d : k_d ≠ 0) :
    A / (S + A) = (k_ad / k_d) * P / (1 + (k_ad / k_d) * P) :=
  langmuir_single_site (K := ℚ) P k_ad k_d A S hreaction hS hk_d

end Adsorption

namespace Thermo

open HeytingLean.Chem.Theories.Thermo

example (params : IdealGasParams ℚ) (n T P1 V1 P2 V2 : ℚ)
    (h1 : IdealGasLaw P1 V1 n T params)
    (h2 : IdealGasLaw P2 V2 n T params) :
    P1 * V1 = P2 * V2 :=
  boylesLaw (K := ℚ) params n T P1 V1 P2 V2 h1 h2

end Thermo

end Tests
end Chem
end HeytingLean
