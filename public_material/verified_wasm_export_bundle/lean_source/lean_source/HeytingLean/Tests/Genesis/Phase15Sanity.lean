import HeytingLean.Genesis

/-!
# Genesis Phase 15 Sanity

Complex-iterant and Pauli bridge checks.
-/

namespace HeytingLean.Tests.Genesis

open HeytingLean.Genesis
open HeytingLean.Quantum.Contextuality.Pauli

#check iterantToMatrix
#check iterant_to_matrix_mul
#check shift_conjugates_iterantToMatrix
#check phaseI_to_phaseJ_by_shift_conjugation
#check pauliObservable
#check crossCoupled_reentry_imaginary

example (x y : CIterant) :
    iterantToMatrix (x * y) = iterantToMatrix x * iterantToMatrix y := by
  exact iterant_to_matrix_mul x y

example :
    shiftMatrix * iterantToMatrix phaseIComplex * shiftMatrix = iterantToMatrix phaseJComplex := by
  exact phaseI_to_phaseJ_by_shift_conjugation

example : σx * σx = (1 : Mat2) := by
  simpa using sigma_x_sq

example : σy * σy = (1 : Mat2) := by
  simpa using sigma_y_sq

example : σz * σz = (1 : Mat2) := by
  simpa using sigma_z_sq

example : σx * σz = - (σz * σx) := by
  simpa using sigma_x_mul_sigma_z_eq_neg_sigma_z_mul_sigma_x

example : σz * σx = (Complex.I : Complex) • σy := by
  simpa using crossCoupled_reentry_imaginary

end HeytingLean.Tests.Genesis
