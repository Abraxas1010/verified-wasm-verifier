import HeytingLean.Constructor.Core

namespace HeytingLean
namespace Tests
namespace Constructor

open HeytingLean.Constructor

universe u

variable {α : Type u} [CompleteLattice α]

variable (R : Nucleus α) (a : α)

/-- Smoke-test for the `possible` / `impossible` interface: the exclusivity
lemma compiles and can be used in a tiny example. -/
example (h : possible R a) : ¬ impossible R a :=
  exclusive R a h

end Constructor
end Tests
end HeytingLean

