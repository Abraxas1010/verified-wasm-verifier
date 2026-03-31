import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Log
import HeytingLean.StackTheory.Stack.MLA

namespace HeytingLean.StackTheory

variable {Φ : Type*} [DecidableEq Φ] [Fintype Φ]

/-- Bennett §5: A viability task is a task viewed through its viable outputs. -/
structure ViabilityTask (v : Vocabulary Φ) extends VTask v

/-- Bennett §5: Viable continuations are the viable outputs compatible with a policy. -/
def viableContinuations (v : Vocabulary Φ) (μ : ViabilityTask v) (π : Finset (Program Φ)) :
    Finset (Finset (Program Φ)) :=
  μ.outputs.filter (fun o => o ∈ extension v π)

/-- Bennett §5: Viability weakness is the number of viable continuations. -/
def viabilityWeakness (v : Vocabulary Φ) (μ : ViabilityTask v) (π : Finset (Program Φ)) : ℕ :=
  (viableContinuations v μ π).card

/-- Bennett §5: Free energy under the uniform viability prior. -/
def freeEnergy (v : Vocabulary Φ) (μ : ViabilityTask v) (π : Finset (Program Φ)) : ℤ :=
  (Nat.log 2 μ.outputs.card : ℤ) - (Nat.log 2 (viabilityWeakness v μ π) : ℤ)

/-- Bennett §5: Viable continuations are contained in the policy extension. -/
theorem viableContinuations_subset_extension (v : Vocabulary Φ) (μ : ViabilityTask v)
    (π : Finset (Program Φ)) :
    viableContinuations v μ π ⊆ extension v π := by
  intro o ho
  exact (Finset.mem_filter.mp ho).2

/-- Bennett §5: viability weakness is bounded by ordinary weakness. -/
theorem viabilityWeakness_le_weakness (v : Vocabulary Φ) (μ : ViabilityTask v)
    (π : Finset (Program Φ)) :
    viabilityWeakness v μ π ≤ weakness v π := by
  exact Finset.card_le_card (viableContinuations_subset_extension v μ π)

/-- Bennett ESM §9.5: ordering policies by log-viability-width is equivalent to
ordering them by the counting free energy. With `Nat.log`, this is the exact
monotone statement available in the discrete setting. -/
theorem wmaxing_eq_fe_min (v : Vocabulary Φ) (μ : ViabilityTask v)
    (π₁ π₂ : Finset (Program Φ)) :
    Nat.log 2 (viabilityWeakness v μ π₁) ≤ Nat.log 2 (viabilityWeakness v μ π₂) ↔
    freeEnergy v μ π₂ ≤ freeEnergy v μ π₁ := by
  constructor
  · intro hWeak
    have hLog :
        (Nat.log 2 (viabilityWeakness v μ π₁) : ℤ) ≤
          (Nat.log 2 (viabilityWeakness v μ π₂) : ℤ) :=
      Int.ofNat_le.mpr hWeak
    simpa [freeEnergy, sub_eq_add_neg] using
      add_le_add_left (Int.neg_le_neg hLog) (Nat.log 2 μ.outputs.card : ℤ)
  · intro hFE
    have hLog :
        (Nat.log 2 (viabilityWeakness v μ π₁) : ℤ) ≤
          (Nat.log 2 (viabilityWeakness v μ π₂) : ℤ) := by
      have := hFE
      simpa [freeEnergy, sub_eq_add_neg] using this
    exact Int.ofNat_le.mp hLog

/-- Bennett ESM exactness refinement: on dyadic continuation counts, the discrete base-2 log
ordering is equivalent to the underlying viability-width ordering. This shows that the `Nat.log`
discretization is tight whenever the relevant widths are powers of two. -/
theorem log_two_order_exact_on_powers_of_two
    {w₁ w₂ k₁ k₂ : ℕ}
    (hw₁ : w₁ = 2 ^ k₁) (hw₂ : w₂ = 2 ^ k₂) :
    Nat.log 2 w₁ ≤ Nat.log 2 w₂ ↔ w₁ ≤ w₂ := by
  subst hw₁
  subst hw₂
  rw [Nat.log_pow Nat.one_lt_two, Nat.log_pow Nat.one_lt_two]
  constructor
  · intro h
    exact Nat.pow_le_pow_right (by decide) h
  · intro h
    exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).mp h

/-- Bennett ESM exactness refinement: when both viability widths are dyadic, minimizing the
counting free energy is equivalent to maximizing the actual viability width. -/
theorem wmaxing_eq_fe_min_of_power_of_two
    (v : Vocabulary Φ) (μ : ViabilityTask v)
    (π₁ π₂ : Finset (Program Φ))
    (hPow₁ : ∃ k₁, viabilityWeakness v μ π₁ = 2 ^ k₁)
    (hPow₂ : ∃ k₂, viabilityWeakness v μ π₂ = 2 ^ k₂) :
    viabilityWeakness v μ π₁ ≤ viabilityWeakness v μ π₂ ↔
    freeEnergy v μ π₂ ≤ freeEnergy v μ π₁ := by
  rcases hPow₁ with ⟨k₁, hk₁⟩
  rcases hPow₂ with ⟨k₂, hk₂⟩
  constructor
  · intro hWeak
    have hLog :
        Nat.log 2 (viabilityWeakness v μ π₁) ≤
          Nat.log 2 (viabilityWeakness v μ π₂) :=
      (log_two_order_exact_on_powers_of_two hk₁ hk₂).2 hWeak
    exact (wmaxing_eq_fe_min v μ π₁ π₂).1 hLog
  · intro hFE
    have hLog :
        Nat.log 2 (viabilityWeakness v μ π₁) ≤
          Nat.log 2 (viabilityWeakness v μ π₂) :=
      (wmaxing_eq_fe_min v μ π₁ π₂).2 hFE
    exact (log_two_order_exact_on_powers_of_two hk₁ hk₂).1 hLog

/-- Bennett Corollary 5.1: free energy is bounded below by the delegated extension width. -/
theorem delegation_bottleneck_fe (v : Vocabulary Φ) (μ : ViabilityTask v)
    (π : Finset (Program Φ)) :
    freeEnergy v μ π ≥ (Nat.log 2 μ.outputs.card : ℤ) - (weakness v π : ℤ) := by
  have hLogLeWeak :
      (Nat.log 2 (viabilityWeakness v μ π) : ℤ) ≤ (weakness v π : ℤ) := by
    exact Int.ofNat_le.mpr ((Nat.log_le_self 2 _).trans (viabilityWeakness_le_weakness v μ π))
  simpa [freeEnergy, sub_eq_add_neg] using
    add_le_add_left (Int.neg_le_neg hLogLeWeak) (Nat.log 2 μ.outputs.card : ℤ)

end HeytingLean.StackTheory
