import Mathlib.Data.Matrix.Basic

/-!
# Genesis.Iterant

Two-phase iterant algebra for Genesis Phase 1.
-/

namespace HeytingLean.Genesis

/-- An iterant carries even/odd phase values. -/
structure Iterant (α : Type*) where
  even : α
  odd : α
deriving Repr, DecidableEq

namespace Iterant

/-- Temporal phase shift. -/
def shift (i : Iterant α) : Iterant α :=
  ⟨i.odd, i.even⟩

@[simp] theorem shift_even (i : Iterant α) : (shift i).even = i.odd := rfl
@[simp] theorem shift_odd (i : Iterant α) : (shift i).odd = i.even := rfl
@[simp] theorem shift_shift (i : Iterant α) : shift (shift i) = i := by
  cases i
  rfl

instance [Inhabited α] : Inhabited (Iterant α) := ⟨⟨default, default⟩⟩

instance [Mul α] : Mul (Iterant α) where
  mul x y := ⟨x.even * y.even, x.odd * y.odd⟩

@[simp] theorem mul_even [Mul α] (x y : Iterant α) : (x * y).even = x.even * y.even := rfl
@[simp] theorem mul_odd [Mul α] (x y : Iterant α) : (x * y).odd = x.odd * y.odd := rfl

/-- Shift-twisted multiplication used in two-phase dynamics. -/
def mulShifted [Mul α] (x y : Iterant α) : Iterant α :=
  ⟨x.even * y.odd, x.odd * y.even⟩

/-- Diagonal matrix representation of an iterant. -/
def toDiagMatrix [Zero α] (i : Iterant α) : Matrix (Fin 2) (Fin 2) α :=
  fun r c =>
    match r.1, c.1 with
    | 0, 0 => i.even
    | 1, 1 => i.odd
    | _, _ => 0

@[simp] theorem toDiagMatrix_00 [Zero α] (i : Iterant α) :
    toDiagMatrix i ⟨0, by decide⟩ ⟨0, by decide⟩ = i.even := rfl

@[simp] theorem toDiagMatrix_11 [Zero α] (i : Iterant α) :
    toDiagMatrix i ⟨1, by decide⟩ ⟨1, by decide⟩ = i.odd := rfl

end Iterant

/-- Canonical phase I: `[false, true]`. -/
def phaseI : Iterant Bool := ⟨false, true⟩

/-- Canonical phase J: `[true, false]`. -/
def phaseJ : Iterant Bool := ⟨true, false⟩

theorem phaseJ_eq_shift_phaseI : phaseJ = Iterant.shift phaseI := rfl
theorem phaseI_eq_shift_phaseJ : phaseI = Iterant.shift phaseJ := rfl
theorem phaseI_ne_phaseJ : phaseI ≠ phaseJ := by decide

end HeytingLean.Genesis
