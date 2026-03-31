import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic
import HeytingLean.Bridge.Veselov.HybridZeckendorf.FibIdentities

/-!
# Bridge.Veselov.HybridZeckendorf.FibSemigroup

Structural compatibility stub for Vladimir's Fibonacci semigroup over (0,1].

The semigroup S is generated additively by:
- Fibonacci numbers F_n (integer part, already formalized in HybridNumber)
- Telescopic parts p_n = F_n / (F_{n+1} · F_{n+2}) = 1/F_{n+1} - 1/F_{n+2}

This file verifies that the semigroup types are compatible with the existing
HZ infrastructure. It defines the core structure and evaluation maps (all
proved without gaps). The semigroup addition operation and its correctness theorem
are documented as future obligations below — they require formalizing the
Zeckendorf normalization algorithm for the parts basis.

## Future Obligations (not formalized here)
- `FibSemigroup.add`: concatenate + normalize (Python impl in
  `scripts/fibonacci_semigroup_utility_test.py:normalize_zeckendorf`)
- `FibSemigroup.eval_add`: value preservation under addition
- `telescopic_sum_identity`: Σ p_n = 1 - 1/F_{N+2} (confirmed analytically
  in Phase 1 of the utility test)

Created by: fibonacci_semigroup_utility_test (Step 3.4)
Conjecture: fibonacci_semigroup_utility_20260330 (resolved: boring)
-/

namespace HeytingLean.Bridge.Veselov.HybridZeckendorf

/-- Part index set with the Zeckendorf no-consecutive constraint.
    Represents a value in (0,1] as Σ p_n for n ∈ indices. -/
structure FibSemigroup where
  /-- Fibonacci indices used (integer part — delegates to HybridNumber). -/
  fibs : List Nat
  /-- Part indices used (fractional part in (0,1]). -/
  parts : List Nat
  /-- Zeckendorf constraint: no two consecutive indices in `parts`. -/
  no_consec : ∀ i, i ∈ parts → (i + 1) ∉ parts
  deriving Repr

/-- The telescopic part p_n = 1/F_{n+1} - 1/F_{n+2}, as a rational.
    Requires n ≥ 1 and F_{n+1}, F_{n+2} > 0. -/
noncomputable def partRat (n : Nat) (_hn : n ≥ 1) : ℚ :=
  1 / (Nat.fib (n + 1) : ℚ) - 1 / (Nat.fib (n + 2) : ℚ)

/-- Evaluate the fractional part of a FibSemigroup element as a rational.
    Returns Σ_{n ∈ parts} p_n. -/
noncomputable def FibSemigroup.evalParts (s : FibSemigroup) : ℚ :=
  (s.parts.map fun n => 1 / (Nat.fib (n + 1) : ℚ) - 1 / (Nat.fib (n + 2) : ℚ)).sum

/-- Evaluate the integer part via existing Fibonacci sum. -/
def FibSemigroup.evalFibs (s : FibSemigroup) : Nat :=
  (s.fibs.map Nat.fib).sum

/-- Full evaluation: integer part + fractional part. -/
noncomputable def FibSemigroup.eval (s : FibSemigroup) : ℚ :=
  (s.evalFibs : ℚ) + s.evalParts

/-- The empty semigroup element (zero fibs, zero parts). -/
def FibSemigroup.empty : FibSemigroup where
  fibs := []
  parts := []
  no_consec := by simp

/-- The empty element evaluates to zero. -/
theorem FibSemigroup.eval_empty : FibSemigroup.empty.eval = 0 := by
  simp [FibSemigroup.eval, FibSemigroup.evalFibs, FibSemigroup.evalParts,
        FibSemigroup.empty]

/-- A singleton fibs element evaluates to F_n. -/
theorem FibSemigroup.evalFibs_singleton (n : Nat) :
    (FibSemigroup.mk [n] [] (by simp)).evalFibs = Nat.fib n := by
  simp [FibSemigroup.evalFibs]

end HeytingLean.Bridge.Veselov.HybridZeckendorf
