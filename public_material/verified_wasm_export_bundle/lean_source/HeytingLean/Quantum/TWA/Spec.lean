import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# TWA specification core (Phase 9, spec-first)

This module provides a minimal algebraic core for spin-based dynamics used by
TWA-style approximations:

- spins as `Fin 3 → ℝ`,
- dot product and cross product,
- orthogonality facts implying norm preservation for Hamiltonian vector fields
  of the form `ṡ = s × v`.

No stochastic calculus or differential equation theory is formalized here.
-/

namespace HeytingLean
namespace Quantum
namespace TWA

open scoped BigOperators

/-- A 3D spin vector. -/
abbrev SpinVec : Type := Fin 3 → ℝ

def dot (a b : SpinVec) : ℝ :=
  ∑ i : Fin 3, a i * b i

def normSq (s : SpinVec) : ℝ :=
  dot s s

/-- Explicit cross product on `Fin 3 → ℝ` with coordinates `(0,1,2)`. -/
def cross (a b : SpinVec) : SpinVec :=
  fun i =>
    match i.1 with
    | 0 => a 1 * b 2 - a 2 * b 1
    | 1 => a 2 * b 0 - a 0 * b 2
    | _ => a 0 * b 1 - a 1 * b 0

@[simp] theorem cross_0 (a b : SpinVec) : cross a b 0 = a 1 * b 2 - a 2 * b 1 := rfl
@[simp] theorem cross_1 (a b : SpinVec) : cross a b 1 = a 2 * b 0 - a 0 * b 2 := rfl
@[simp] theorem cross_2 (a b : SpinVec) : cross a b 2 = a 0 * b 1 - a 1 * b 0 := rfl

theorem dot_cross_self (a b : SpinVec) : dot a (cross a b) = 0 := by
  simp [dot, cross, Fin.sum_univ_three]
  ring

theorem dot_self_cross (a b : SpinVec) : dot (cross a b) b = 0 := by
  simp [dot, cross, Fin.sum_univ_three]
  ring

/-- Hamiltonian-style vector field `ṡ = s × v`. -/
def hamiltonianVF (v : SpinVec) (s : SpinVec) : SpinVec :=
  cross s v

theorem dot_self_hamiltonianVF (v s : SpinVec) : dot s (hamiltonianVF v s) = 0 := by
  simpa [hamiltonianVF] using dot_cross_self s v

end TWA
end Quantum
end HeytingLean

