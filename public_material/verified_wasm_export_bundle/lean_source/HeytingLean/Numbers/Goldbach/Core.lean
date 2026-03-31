import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Ring.Parity

/-
# Goldbach core predicates

This module introduces a small, self-contained core for working with
Goldbach-style statements inside HeytingLean.  It is deliberately
conservative: we define predicates and bounded variants, but we do
**not** assert any global Goldbach theorems.
-/

namespace HeytingLean
namespace Numbers
namespace Goldbach

/-- A Goldbach pair for an even number `n`: two primes whose sum is `n`. -/
def isGoldbachPair (n p q : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime q ∧ n = p + q

/-- A Goldbach triple for an odd number `n`: three primes whose sum is `n`. -/
def isGoldbachTriple (n p q r : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r

/-- Strong Goldbach conjecture, stated as a `Prop` (not assumed). -/
def StrongGoldbach : Prop :=
  ∀ n : ℕ, 4 ≤ n ∧ Even n → ∃ p q, isGoldbachPair n p q

/-- Weak Goldbach conjecture, stated as a `Prop` (not assumed). -/
def WeakGoldbach : Prop :=
  ∀ n : ℕ, 7 ≤ n ∧ Odd n → ∃ p q r, isGoldbachTriple n p q r

/-- Bounded strong Goldbach: every even `4 ≤ n ≤ N` has a Goldbach pair. -/
def strongGoldbachUpTo (N : ℕ) : Prop :=
  ∀ n : ℕ, 4 ≤ n ∧ Even n ∧ n ≤ N → ∃ p q, isGoldbachPair n p q

/-- Bounded weak Goldbach: every odd `7 ≤ n ≤ N` has a Goldbach triple. -/
def weakGoldbachUpTo (N : ℕ) : Prop :=
  ∀ n : ℕ, 7 ≤ n ∧ Odd n ∧ n ≤ N → ∃ p q r, isGoldbachTriple n p q r

end Goldbach
end Numbers
end HeytingLean
