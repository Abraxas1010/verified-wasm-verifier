import HeytingLean.Coalgebra.Universal

/-!
# Coalgebra.Universal sanity

This module ensures the lightweight universal-coalgebra layer compiles as part of the
standard `HeytingLean.Tests.AllSanity` umbrella.
-/

namespace HeytingLean
namespace Tests
namespace Coalgebra

-- Import is the test; keep additional checks lightweight.

#check HeytingLean.Coalgebra.Universal.Coalg
#check HeytingLean.Coalgebra.Universal.RelBisim.Bisimilar

-- Mealy finality + behavioral equivalence (general state machines).
#check HeytingLean.Coalgebra.Universal.Examples.mealyFinalCoalgebra_isTerminal
#check HeytingLean.Coalgebra.Universal.Examples.MealyFinal.bisimilar_iff_sem_eq

end Coalgebra
end Tests
end HeytingLean
