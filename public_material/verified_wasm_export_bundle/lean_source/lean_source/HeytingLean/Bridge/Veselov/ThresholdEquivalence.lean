import Mathlib.Data.Nat.Factorial.Basic

/-!
# Bridge.Veselov.ThresholdEquivalence

Constructive P4 bridge surface:
- factorial-vs-power threshold inequality,
- packaged as a ratchet-style growth law.
-/

namespace HeytingLean.Bridge.Veselov

/-- P4 core inequality: shifted factorial dominates fixed-power growth. -/
theorem factorial_shift_dominates_power (M k : ℕ) :
    M ^ k ≤ Nat.factorial (M + k) := by
  have hmul :
      Nat.factorial M * M ^ k ≤ Nat.factorial (M + k) := by
    simpa [Nat.add_sub_cancel] using
      (Nat.factorial_mul_pow_sub_le_factorial
        (n := M) (m := M + k) (Nat.le_add_right M k))
  have hpow : M ^ k ≤ Nat.factorial M * M ^ k := by
    calc
      M ^ k ≤ M ^ k * Nat.factorial M :=
        Nat.le_mul_of_pos_right (M ^ k) (Nat.factorial_pos M)
      _ = Nat.factorial M * M ^ k := by simp [Nat.mul_comm]
  exact le_trans hpow hmul

/-- Growth-threshold form used by bridge narratives (`M!` outruns `M^k` after shift). -/
theorem threshold_growth_law (M k : ℕ) :
    M ^ k ≤ Nat.factorial (M + k) :=
  factorial_shift_dominates_power M k

/-- Asymptotic wrapper: for each fixed `k`, dominance holds eventually (in fact from `0`). -/
theorem factorial_dominates_power_eventually (k : ℕ) :
    ∃ N : ℕ, ∀ M ≥ N, M ^ k ≤ Nat.factorial (M + k) := by
  refine ⟨0, ?_⟩
  intro M _hM
  exact threshold_growth_law M k

/-- Diagonal wrapper used by growth-threshold narratives. -/
theorem threshold_growth_law_diagonal (M : ℕ) :
    M ^ M ≤ Nat.factorial (M + M) :=
  threshold_growth_law M M

end HeytingLean.Bridge.Veselov
