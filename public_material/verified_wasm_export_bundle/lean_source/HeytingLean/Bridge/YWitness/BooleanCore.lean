import HeytingLean.Genesis.YWitness.Foundations
import HeytingLean.LoF.Bauer.DoubleNegation

namespace HeytingLean.Bridge.YWitness

open HeytingLean.LoF.Bauer
open Heyting

/-- The discrete side is identified with Heyting-regular elements. -/
def isDiscrete {α : Type _} [HeytingAlgebra α] (a : α) : Prop :=
  IsRegular a

theorem discrete_iff_dn_fixed {α : Type _} [HeytingAlgebra α] (a : α) :
    isDiscrete a <-> doubleNegNucleus α a = a := by
  simpa [isDiscrete] using (doubleNegNucleus_fixed_iff (α := α) (a := a)).symm

theorem classical_core_is_discrete_side {α : Type _} [HeytingAlgebra α]
    (a : ClassicalCore α) : isDiscrete (a : α) := by
  exact a.property

theorem regularized_value_is_discrete {α : Type _} [HeytingAlgebra α] (a : α) :
    isDiscrete ((toClassicalCore α a : ClassicalCore α) : α) := by
  exact (toClassicalCore α a).property

end HeytingLean.Bridge.YWitness
