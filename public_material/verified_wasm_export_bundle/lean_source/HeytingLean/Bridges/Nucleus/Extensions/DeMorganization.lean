import HeytingLean.LoF.Bauer.DoubleNegation

namespace HeytingLean
namespace Bridges
namespace Nucleus
namespace Extensions

open Heyting

/-- Scoped v1 DeMorganization nucleus: implemented via the established double-negation nucleus. -/
def deMorganizationNucleus (α : Type*) [HeytingAlgebra α] : _root_.Nucleus α :=
  HeytingLean.LoF.Bauer.doubleNegNucleus α

@[simp] theorem deMorganization_apply (α : Type*) [HeytingAlgebra α] (a : α) :
    deMorganizationNucleus α a = aᶜᶜ := by
  rfl

@[simp] theorem deMorganization_eq_doubleNeg (α : Type*) [HeytingAlgebra α] :
    deMorganizationNucleus α = HeytingLean.LoF.Bauer.doubleNegNucleus α := rfl

/-- Fixed points of the scoped DeMorganization nucleus are regular elements. -/
@[simp] theorem deMorganization_fixed_iff_regular
    (α : Type*) [HeytingAlgebra α] (a : α) :
    deMorganizationNucleus α a = a ↔ IsRegular a := by
  simpa [deMorganizationNucleus] using
    (HeytingLean.LoF.Bauer.doubleNegNucleus_fixed_iff (α := α) a)

/-- On Boolean algebras, scoped DeMorganization collapses to identity. -/
@[simp] theorem deMorganization_eq_id_on_boolean
    (α : Type*) [BooleanAlgebra α] :
    deMorganizationNucleus α = (⊥ : _root_.Nucleus α) := by
  ext a
  simp [deMorganizationNucleus]

end Extensions
end Nucleus
end Bridges
end HeytingLean
