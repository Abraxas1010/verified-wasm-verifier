import HeytingLean.Calculus.CalculusLens

/-!
CalculusLens wrapper around a `CalculusNucleus` to mirror lens-style
organization used elsewhere in the project.
-/

namespace HeytingLean
namespace Calculus

universe u

structure CalculusLens (α : Type u) [CompleteLattice α] where
  N : CalculusNucleus α

namespace CalculusLens

variable {α : Type u} [CompleteLattice α]

def Omega (L : CalculusLens α) : Set α := L.N.Omega

@[simp] lemma mem_Omega {L : CalculusLens α} {a : α} :
    a ∈ L.Omega ↔ L.N.R a = a := Iff.rfl

end CalculusLens

end Calculus
end HeytingLean

