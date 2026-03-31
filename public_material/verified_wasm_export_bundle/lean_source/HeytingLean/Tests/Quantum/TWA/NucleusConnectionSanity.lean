import Mathlib.Data.Set.Lattice
import HeytingLean.Quantum.TWA.NucleusConnection

namespace HeytingLean
namespace Tests
namespace Quantum
namespace TWA

open HeytingLean.Quantum.TWA

/-!
Sanity checks for the order-theoretic nucleus connection layer.
-/

namespace SetNucleusDemo

open scoped Classical

def unionInfHom (F : Set Nat) : InfHom (Set Nat) (Set Nat) where
  toFun := fun S => S ∪ F
  map_inf' := by
    intro S T
    ext x
    constructor
    · intro hx
      rcases hx with hx | hx
      · exact And.intro (Or.inl hx.1) (Or.inl hx.2)
      · exact And.intro (Or.inr hx) (Or.inr hx)
    · intro hx
      rcases hx with ⟨hx1, hx2⟩
      rcases hx1 with hx1 | hxF
      · rcases hx2 with hx2 | hxF2
        · exact Or.inl ⟨hx1, hx2⟩
        · exact Or.inr hxF2
      · exact Or.inr hxF

def unionNucleus (F : Set Nat) : Nucleus (Set Nat) :=
  Nucleus.mk (unionInfHom F)
    (idempotent' := by
      intro S x hx
      rcases hx with hx | hx
      · exact hx
      · exact Or.inr hx)
    (le_apply' := by
      intro S x hx
      exact Or.inl hx)

@[simp] lemma unionNucleus_apply (F S : Set Nat) : unionNucleus F S = S ∪ F := rfl

end SetNucleusDemo

open SetNucleusDemo

def F : Set Nat := {0}
def R : Nucleus (Set Nat) := unionNucleus F

example (S : Set Nat) : (S ∈ R.toSublocale) ↔ R S = S := by
  simpa using mem_toSublocale_iff_fixed (R := R) S

example (S : Set Nat) : (S ∪ F) ∈ codeSpaceSet R := by
  simp [codeSpaceSet, R, SetNucleusDemo.unionNucleus_apply, F]

example (S : Set Nat) : R (S ⇨ F) = S ⇨ F := by
  have hF : R F = F := by
    simp [R, F, SetNucleusDemo.unionNucleus_apply]
  simpa using himp_fixed_of_fixed_right (R := R) (x := S) (y := F) hF

end TWA
end Quantum
end Tests
end HeytingLean

