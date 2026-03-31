import HeytingLean.Genesis.Iterant
import HeytingLean.Quantum.Contextuality.MerminPeresRealization
import Mathlib.Data.Complex.Basic

/-!
# Genesis.IterantComplex

First-attempt complex extension of iterants and Pauli-bridge lemmas.
-/

noncomputable section

namespace HeytingLean.Genesis

open HeytingLean.Quantum.Contextuality
open HeytingLean.Quantum.Contextuality.Pauli
open Matrix

abbrev CIterant := Iterant Complex
abbrev Mat2 := HeytingLean.Quantum.Contextuality.Mat2

/-- Diagonal matrix representation of a complex iterant. -/
def iterantToMatrix (i : CIterant) : Mat2 :=
  Iterant.toDiagMatrix i

@[simp] theorem iterantToMatrix_even (a b : Complex) :
    iterantToMatrix ⟨a, b⟩ ⟨0, by decide⟩ ⟨0, by decide⟩ = a := by
  rfl

@[simp] theorem iterantToMatrix_odd (a b : Complex) :
    iterantToMatrix ⟨a, b⟩ ⟨1, by decide⟩ ⟨1, by decide⟩ = b := by
  rfl

/-- Shift matrix that swaps even/odd phases. -/
def shiftMatrix : Mat2 :=
  fun i j =>
    if i = 0 ∧ j = 1 then (1 : Complex)
    else if i = 1 ∧ j = 0 then (1 : Complex)
    else 0

/-- `shiftMatrix` coincides with Pauli `σx`. -/
@[simp] theorem shiftMatrix_eq_sigmaX : shiftMatrix = σx := by
  rfl

@[simp] theorem shiftMatrix_sq : shiftMatrix * shiftMatrix = (1 : Mat2) := by
  simpa [shiftMatrix_eq_sigmaX] using Pauli.σx_sq

/-- Complex phase-pole seeds for the two-phase witness. -/
def phaseIComplex : CIterant := ⟨(1 : Complex), (-1 : Complex)⟩
def phaseJComplex : CIterant := Iterant.shift phaseIComplex

@[simp] theorem phaseJComplex_def : phaseJComplex = ⟨(-1 : Complex), (1 : Complex)⟩ := by
  rfl

/-- Observable matrix assembled from Pauli generators. -/
def pauliObservable (x y z : Complex) : Mat2 :=
  x • σx + y • σy + z • σz

/-- Diagonal embedding is multiplicative for iterant pointwise product. -/
theorem iterant_to_matrix_mul (x y : CIterant) :
    iterantToMatrix (x * y) = iterantToMatrix x * iterantToMatrix y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [iterantToMatrix, Iterant.toDiagMatrix, Matrix.mul_apply]

/-- Re-entry transport: shift-conjugation swaps even/odd phase coordinates. -/
theorem shift_conjugates_iterantToMatrix (i : CIterant) :
    shiftMatrix * iterantToMatrix i * shiftMatrix = iterantToMatrix (Iterant.shift i) := by
  cases i with
  | mk ie io =>
    ext r c
    fin_cases r <;> fin_cases c <;>
      simp [σx, iterantToMatrix, Iterant.toDiagMatrix, Matrix.mul_apply]

theorem phaseI_to_phaseJ_by_shift_conjugation :
    shiftMatrix * iterantToMatrix phaseIComplex * shiftMatrix = iterantToMatrix phaseJComplex := by
  simpa [phaseJComplex] using shift_conjugates_iterantToMatrix phaseIComplex

theorem phaseJ_to_phaseI_by_shift_conjugation :
    shiftMatrix * iterantToMatrix phaseJComplex * shiftMatrix = iterantToMatrix phaseIComplex := by
  simpa [phaseJComplex, Iterant.shift_shift] using
    (shift_conjugates_iterantToMatrix (i := phaseJComplex))

theorem shift_conjugation_involutive (i : CIterant) :
    shiftMatrix * (shiftMatrix * iterantToMatrix i * shiftMatrix) * shiftMatrix =
      iterantToMatrix i := by
  calc
    shiftMatrix * (shiftMatrix * iterantToMatrix i * shiftMatrix) * shiftMatrix
        = σx * σx * iterantToMatrix i * (σx * σx) := by
            simp [shiftMatrix_eq_sigmaX, Matrix.mul_assoc]
    _ = (1 : Mat2) * iterantToMatrix i * (1 : Mat2) := by
          simp [Pauli.σx_sq]
    _ = iterantToMatrix i := by simp

/-- Existing Pauli-square law exposed in Genesis namespace. -/
theorem sigma_x_sq : σx * σx = (1 : Mat2) :=
  Pauli.σx_sq

/-- Existing Pauli-square law exposed in Genesis namespace. -/
theorem sigma_y_sq : σy * σy = (1 : Mat2) :=
  Pauli.σy_sq

/-- Existing Pauli-square law exposed in Genesis namespace. -/
theorem sigma_z_sq : σz * σz = (1 : Mat2) :=
  Pauli.σz_sq

/-- Cross-coupled relation: `σzσx = iσy`. -/
theorem sigma_z_mul_sigma_x : σz * σx = (Complex.I : Complex) • σy :=
  Pauli.σz_mul_σx

/-- Cross-coupled relation: `σxσz = -iσy`. -/
theorem sigma_x_mul_sigma_z : σx * σz = (-Complex.I : Complex) • σy :=
  Pauli.σx_mul_σz

/-- Cross-coupled relation: `σxσy = iσz`. -/
theorem sigma_x_mul_sigma_y : σx * σy = (Complex.I : Complex) • σz := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σx, σy, σz, Matrix.mul_apply]

/-- Cross-coupled relation: `σyσx = -iσz`. -/
theorem sigma_y_mul_sigma_x : σy * σx = (-Complex.I : Complex) • σz := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σx, σy, σz, Matrix.mul_apply]

/-- Anticommutation witness for `σx` and `σz`. -/
theorem sigma_x_mul_sigma_z_eq_neg_sigma_z_mul_sigma_x :
    σx * σz = - (σz * σx) := by
  calc
    σx * σz = (-Complex.I : Complex) • σy := sigma_x_mul_sigma_z
    _ = -((Complex.I : Complex) • σy) := by
      ext i j
      simp
    _ = - (σz * σx) := by
      simp [sigma_z_mul_sigma_x]

/-- Anticommutation witness for `σx` and `σy`. -/
theorem sigma_x_mul_sigma_y_eq_neg_sigma_y_mul_sigma_x :
    σx * σy = - (σy * σx) := by
  calc
    σx * σy = (Complex.I : Complex) • σz := sigma_x_mul_sigma_y
    _ = -((-Complex.I : Complex) • σz) := by
      ext i j
      simp
    _ = - (σy * σx) := by
      simp [sigma_y_mul_sigma_x]

/-- First-attempt "imaginary from cross-coupled re-entry" statement. -/
theorem crossCoupled_reentry_imaginary :
    σz * σx = (Complex.I : Complex) • σy :=
  sigma_z_mul_sigma_x

end HeytingLean.Genesis
