import Mathlib.Order.Category.HeytAlg

/-
Small wrapper exposing the mathlib category of Heyting algebras under the
project-local name `HeytingCat`.  This keeps the Direction 6 categorical plan
close to the blueprint while delegating all categorical structure to mathlib.
-/

namespace HeytingLean
namespace LoF

abbrev HeytingCat := HeytAlg

end LoF
end HeytingLean

