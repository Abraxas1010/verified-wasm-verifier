import HeytingLean.Numbers.Surreal.ComparisonCore

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Numbers.Surreal
open HeytingLean.Numbers.SurrealCore

/-- Compile-only skeleton for the comparison core via a Galois connection. -/
example {Ωₗ} [CompleteLattice Ωₗ]
    (f : Set PreGame → Ωₗ) (g : Ωₗ → Set PreGame)
    (gc : GaloisConnection f g)
    (S T : Set PreGame) :
    comparisonCore f g gc (S ∩ T) ⊆
      comparisonCore f g gc S ∩ comparisonCore f g gc T := by
  exact comparison_map_inf_le f g gc S T

end Numbers
end Tests
end HeytingLean

