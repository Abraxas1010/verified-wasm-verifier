import HeytingLean.LoF.Bauer

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.LoF

universe u

section DoubleNegation

variable {α : Type u} [HeytingAlgebra α]

example (a : α) : a ≤ Bauer.doubleNegNucleus α a := by
  simpa using (Nucleus.le_apply (n := Bauer.doubleNegNucleus α) (x := a))

example (a : α) : Bauer.doubleNegNucleus α (Bauer.doubleNegNucleus α a) = Bauer.doubleNegNucleus α a := by
  simp

example (a : α) : (Bauer.doubleNegNucleus α a = a ↔ Heyting.IsRegular a) := by
  simpa using (Bauer.doubleNegNucleus_fixed_iff (α := α) a)

example : BooleanAlgebra (Bauer.ClassicalCore α) := by
  infer_instance

end DoubleNegation

section NucleiOrder

variable {α : Type u} [PrimaryAlgebra α]
variable (n m : Nucleus α)

example : HeytingAlgebra (Nucleus α) := by infer_instance
example : CompleteLattice (Nucleus α) := by infer_instance

example : Set.range m ⊆ Set.range n ↔ n ≤ m :=
  Bauer.range_subset_range_iff (n := n) (m := m)

end NucleiOrder

end LoF
end Tests
end HeytingLean
