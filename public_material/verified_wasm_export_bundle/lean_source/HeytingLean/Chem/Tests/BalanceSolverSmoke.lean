import HeytingLean.Chem.Reactions.BalanceSolver
import HeytingLean.Chem.Reactions.Examples
import Mathlib.Tactic

/-!
# Reaction-balancing solver smoke tests

Compile-only checks that the bounded balancer finds coefficients for a few canonical reactions.
-/

namespace HeytingLean
namespace Chem
namespace Tests

open HeytingLean.Chem
open HeytingLean.Chem.Reactions
open HeytingLean.Chem.Reactions.Examples

example : balance? [H2, O2] [H2O] 3 = some ([2, 1], [2]) := by
  native_decide

example : Balanced (mkTerms [2, 1] [H2, O2]) (mkTerms [2] [H2O]) := by
  have h : balance? [H2, O2] [H2O] 3 = some ([2, 1], [2]) := by
    native_decide
  exact balance?_sound (reactants := [H2, O2]) (products := [H2O]) (maxCoeff := 3) h

example : balance? [CH4, O2] [CO2, H2O] 2 = some ([1, 2], [1, 2]) := by
  native_decide

example : Balanced (mkTerms [1, 2] [CH4, O2]) (mkTerms [1, 2] [CO2, H2O]) := by
  have h : balance? [CH4, O2] [CO2, H2O] 2 = some ([1, 2], [1, 2]) := by
    native_decide
  exact balance?_sound (reactants := [CH4, O2]) (products := [CO2, H2O]) (maxCoeff := 2) h

end Tests
end Chem
end HeytingLean

