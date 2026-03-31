import Mathlib.Algebra.Order.Kleene

/-!
# Kleene algebra bridge

We re-export Mathlib's `KleeneAlgebra` in the HeytingLean logic namespace to
make it a first-class integration point for program- and automata-style
reasoning.
-/

namespace HeytingLean
namespace Logic

abbrev KleeneAlg (α : Type*) := KleeneAlgebra α

end Logic
end HeytingLean
