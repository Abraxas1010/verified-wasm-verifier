import HeytingLean.OTM.Basic
import Mathlib.SetTheory.Ordinal.Basic

namespace HeytingLean
namespace OTM

universe u v

/-- Index-parametric OTM tape whose cells are fixed by a selected nucleus. -/
structure Tape (ι : Type u) (α : Type v) [SemilatticeInf α] [OrderBot α]
    (N : RNucleus α) where
  cells : ι → α
  fixed : ∀ i : ι, N.R (cells i) = cells i

namespace Tape

variable {ι : Type u} {α : Type v} [SemilatticeInf α] [OrderBot α]
variable {N : RNucleus α}

/-- Read one tape cell. -/
def read (T : Tape ι α N) (i : ι) : α :=
  T.cells i

/-- Write a fixed value into one tape cell. -/
def write [DecidableEq ι] (T : Tape ι α N) (i : ι) (v : α) (hv : N.R v = v) : Tape ι α N where
  cells := Function.update T.cells i v
  fixed j := by
    by_cases hji : j = i
    · subst hji
      simpa [Function.update] using hv
    · simpa [Function.update, hji] using T.fixed j

@[simp] theorem read_write_same [DecidableEq ι]
    (T : Tape ι α N) (i : ι) (v : α) (hv : N.R v = v) :
    (write T i v hv).read i = v := by
  simp [read, write, Function.update]

@[simp] theorem read_write_other [DecidableEq ι]
    (T : Tape ι α N) (i j : ι) (hij : j ≠ i) (v : α) (hv : N.R v = v) :
    (write T i v hv).read j = T.read j := by
  simp [read, write, Function.update, hij]

@[simp] theorem read_fixed (T : Tape ι α N) (i : ι) :
    N.R (T.read i) = T.read i := by
  simpa [read] using T.fixed i

end Tape

/-- Integer-indexed OTM tape (classical TM-style carrier). -/
abbrev IntTape (α : Type v) [SemilatticeInf α] [OrderBot α] (N : RNucleus α) :=
  Tape Int α N

/-- Nat-indexed OTM tape (one-sided carrier). -/
abbrev NatTape (α : Type v) [SemilatticeInf α] [OrderBot α] (N : RNucleus α) :=
  Tape Nat α N

/-- Ordinal-indexed OTM tape (transfinite carrier). -/
abbrev OrdinalTape (α : Type v) [SemilatticeInf α] [OrderBot α] (N : RNucleus α) :=
  Tape Ordinal α N

end OTM
end HeytingLean
