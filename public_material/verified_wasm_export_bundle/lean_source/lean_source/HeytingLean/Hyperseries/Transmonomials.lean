import Mathlib.RingTheory.HahnSeries.Basic

namespace HeytingLean
namespace Hyperseries

/--
Syntactic transmonomial tower for staged hyperseries development.

This does not yet provide full asymptotic ordering/valuation semantics; it gives
an explicit tower language that we can map into future semantic models.
-/
inductive Transmonomial where
  | one
  | omegaPow (e : ℤ)
  | exp (m : Transmonomial)
  | log (m : Transmonomial)
deriving DecidableEq, Repr

namespace Transmonomial

/-- Structural height in the transmonomial constructor tower. -/
def height : Transmonomial → ℕ
  | .one => 0
  | .omegaPow _ => 1
  | .exp m => height m + 1
  | .log m => height m + 1

@[simp] theorem height_one : height .one = 0 := rfl
@[simp] theorem height_omegaPow (e : ℤ) : height (.omegaPow e) = 1 := rfl
@[simp] theorem height_exp (m : Transmonomial) : height (.exp m) = height m + 1 := rfl
@[simp] theorem height_log (m : Transmonomial) : height (.log m) = height m + 1 := rfl

/-- Iterate `exp` constructors in the transmonomial tower. -/
def iterExp : ℕ → Transmonomial → Transmonomial
  | 0, m => m
  | n + 1, m => .exp (iterExp n m)

/-- Iterate `log` constructors in the transmonomial tower. -/
def iterLog : ℕ → Transmonomial → Transmonomial
  | 0, m => m
  | n + 1, m => .log (iterLog n m)

@[simp] theorem iterExp_zero (m : Transmonomial) : iterExp 0 m = m := rfl
@[simp] theorem iterExp_succ (n : ℕ) (m : Transmonomial) :
    iterExp (n + 1) m = .exp (iterExp n m) := rfl

@[simp] theorem iterLog_zero (m : Transmonomial) : iterLog 0 m = m := rfl
@[simp] theorem iterLog_succ (n : ℕ) (m : Transmonomial) :
    iterLog (n + 1) m = .log (iterLog n m) := rfl

theorem height_iterExp (n : ℕ) (m : Transmonomial) :
    height (iterExp n m) = height m + n := by
  induction n generalizing m with
  | zero =>
      simp
  | succ n ih =>
      simp [iterExp, ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem height_iterLog (n : ℕ) (m : Transmonomial) :
    height (iterLog n m) = height m + n := by
  induction n generalizing m with
  | zero =>
      simp
  | succ n ih =>
      simp [iterLog, ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Embed the existing base exponent lane into the transmonomial language. -/
def ofBaseExponent (e : ℤ) : Transmonomial := .omegaPow e

end Transmonomial

/--
Current executable Hahn-series lane used by existing pilot infrastructure.
We keep this stable as `ℤ` while transmonomial semantics are integrated in parallel.
-/
abbrev BaseExponent : Type := ℤ

/-- Minimal Hahn-series abbreviation over the base exponent type. -/
abbrev Hahn (R : Type*) [Zero R] := HahnSeries BaseExponent R

end Hyperseries
end HeytingLean
