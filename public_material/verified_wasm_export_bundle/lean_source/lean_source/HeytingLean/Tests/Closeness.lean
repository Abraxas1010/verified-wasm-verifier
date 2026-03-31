import HeytingLean.Quantum.Translate.Modality
import HeytingLean.Quantum.Translate.Omega
import HeytingLean.Closeness

/-
  Minimal tests for the Ω_R closeness scaffold.
  These assert that the trivial zero measure yields zero distances.
-/

namespace HeytingLean.Tests

open HeytingLean.Closeness
open HeytingLean.Quantum.Translate

universe u

section

variable {α : Type u} [Order.Frame α] [HeytingAlgebra α]
variable (M : Modality α)

def M0 : OmegaMeasure (M := M) := HeytingLean.Closeness.zeroOmegaMeasure (M := M)

@[simp] theorem dPlusΩ_zero (A B : Omega M) : dPlusΩ (M := M) (Me := M0 M) A B = 0 := rfl

@[simp] theorem dSymΩ_zero (A B : Omega M) : dSymΩ (M := M) (Me := M0 M) A B = 0 := by
  simp [Closeness.dSymΩ, dPlusΩ_zero]

@[simp] theorem dGapΩ_zero (A B : Omega M) : dGapΩ (M := M) (Me := M0 M) A B = 0 := rfl

end

end HeytingLean.Tests
