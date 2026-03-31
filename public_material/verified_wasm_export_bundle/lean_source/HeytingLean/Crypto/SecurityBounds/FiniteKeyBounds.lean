import Mathlib.Data.Real.Basic

/-!
# Finite-key security bounds (interface-first)

This file packages the standard split into correctness and secrecy parameters.
It deliberately avoids probability theory; concrete bounds can be layered later.
-/

namespace HeytingLean
namespace Crypto
namespace SecurityBounds

/-- Finite-key security bookkeeping for QKD. -/
structure FiniteKeyBound where
  /-- Number of signals exchanged. -/
  n_signals : ℕ
  /-- Number of test bits. -/
  n_test : ℕ
  /-- Final key length. -/
  key_length : ℕ
  /-- Correctness parameter. -/
  epsilon_cor : ℝ
  /-- Secrecy parameter. -/
  epsilon_sec : ℝ

namespace FiniteKeyBound

/-- Total security parameter. -/
def epsilon_total (b : FiniteKeyBound) : ℝ :=
  b.epsilon_cor + b.epsilon_sec

@[simp] theorem epsilon_total_eq (b : FiniteKeyBound) :
    b.epsilon_total = b.epsilon_cor + b.epsilon_sec := rfl

end FiniteKeyBound

end SecurityBounds
end Crypto
end HeytingLean

