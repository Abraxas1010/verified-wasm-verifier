import HeytingLean.FractalUniverse.NucleusConnection.SpectralGap

/-!
# Spectral Gap Summability: Cross-Project Re-Export

REUSABLE ABSTRACTION: re-exports SpectralGap convergence/summability
for consumption by downstream projects (Koopman, SafEDMD, etc.).

## How to use

Downstream consumers construct a `SpectralHeytingCorrespondence` with
their specific decay data and immediately inherit:
- `exponential_bound_vanishes`: convergence to 0
- `exponential_bound_summable`: ℓ¹ summability

## Construction recipe

```
{ decay_ratio := Real.exp (-λ₁),
  decay_ratio_pos := Real.exp_pos _,
  decay_ratio_lt_one := <prove exp(-λ₁) < 1 from λ₁ > 0>,
  heyting_gap := your_sequence,
  heyting_gap_nonneg := <your proof>,
  bound_const := C,
  bound_const_pos := <your proof>,
  exponential_bound := <your proof> }
```

The Mathlib chain used internally:
- `exists_pow_lt_of_lt_one → pow_le_pow_of_le_one → squeeze` (vanishes)
- `summable_geometric_of_lt_one → Summable.of_nonneg_of_le` (summable)
-/

namespace HeytingLean.FractalUniverse.Bridges

open NucleusConnection

/-- Re-export: any non-negative sequence bounded by C·rⁿ with r ∈ (0,1)
    converges to 0. Downstream consumers (Koopman, SafEDMD) construct a
    `SpectralHeytingCorrespondence` and call this directly.

    This is the existing `heyting_gap_vanishes` theorem, re-exported
    with documentation for cross-project consumption.
    See SpectralGap.lean for the proof. -/
theorem exponential_bound_vanishes (corr : SpectralHeytingCorrespondence) :
    ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → corr.heyting_gap n < ε :=
  heyting_gap_vanishes corr

/-- Re-export: the bounded sequence is ℓ¹-summable.
    See SpectralGap.lean for the proof. -/
theorem exponential_bound_summable (corr : SpectralHeytingCorrespondence) :
    Summable corr.heyting_gap :=
  heyting_gap_summable corr

end HeytingLean.FractalUniverse.Bridges
