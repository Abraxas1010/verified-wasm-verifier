import HeytingLean.FractalUniverse.Emergence.DiscreteDAlembert
import HeytingLean.FractalUniverse.NucleusConnection.DimFlowAsNucleus
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Spectral Gap ↔ Heyting Gap Correspondence

Connects the spectral gap λ₂ of the discrete d'Alembertian to the
Heyting gap (distance from a geometry to its nucleus image) in the
dimensional flow nucleus framework.

## Structure

`SpectralHeytingCorrespondence` axiomatizes:
- A decay ratio r = exp(-λ₂) ∈ (0,1) encoding a positive spectral gap
- A non-negative Heyting gap function on discrete scales ℕ
- A uniform exponential bound: gap(n) ≤ C · rⁿ

## Derived results

From the uniform exponential bound we derive (genuine real analysis,
not bound weakening):
- `heyting_gap_vanishes`: gap(n) → 0 via squeeze with geometric decay
- `heyting_gap_summable`: Σ gap(n) < ∞ via comparison with geometric series

Source: Veselov's eigenlearner experiments + nucleus interpretation.
-/

namespace HeytingLean.FractalUniverse.NucleusConnection

/-- Correspondence between spectral gap and convergence rate.
    The spectral gap λ₂ is encoded via the decay ratio r = exp(-λ₂) ∈ (0,1).
    The Heyting gap (distance from geometry to its nucleus image) is
    uniformly bounded by C · rⁿ, enabling genuine derivation of
    convergence and summability from the geometric decay structure. -/
structure SpectralHeytingCorrespondence where
  /-- Decay ratio r = exp(-λ₂). Encodes the spectral gap. -/
  decay_ratio : ℝ
  /-- The ratio is positive. -/
  decay_ratio_pos : 0 < decay_ratio
  /-- The ratio is strictly less than 1 (spectral gap is positive). -/
  decay_ratio_lt_one : decay_ratio < 1
  /-- Heyting gap: distance from geometry to its nucleus image at scale n. -/
  heyting_gap : ℕ → ℝ
  /-- The gap is non-negative (it is a distance). -/
  heyting_gap_nonneg : ∀ n, 0 ≤ heyting_gap n
  /-- Bound constant from spectral theory of the graph. -/
  bound_const : ℝ
  /-- The bound constant is positive. -/
  bound_const_pos : 0 < bound_const
  /-- The correspondence: gap is uniformly bounded by C · rⁿ. -/
  exponential_bound : ∀ n, heyting_gap n ≤ bound_const * decay_ratio ^ n

/-- The Heyting gap converges to 0 as scale increases.
    Proof: the geometric bound C · rⁿ → 0 (since r < 1), and the gap
    is squeezed between 0 and C · rⁿ. The key step uses
    `exists_pow_lt_of_lt_one` to find the threshold N where rᴺ < ε/C,
    then `pow_le_pow_of_le_one` to extend to all n ≥ N. -/
theorem heyting_gap_vanishes (corr : SpectralHeytingCorrespondence) :
    ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → corr.heyting_gap n < ε := by
  intro ε hε
  -- Find N with r^N < ε/C
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hε corr.bound_const_pos)
    corr.decay_ratio_lt_one
  refine ⟨N, fun n hn => ?_⟩
  -- r^n ≤ r^N since n ≥ N and r ∈ (0,1)
  have hrn : corr.decay_ratio ^ n ≤ corr.decay_ratio ^ N :=
    pow_le_pow_of_le_one (le_of_lt corr.decay_ratio_pos)
      (le_of_lt corr.decay_ratio_lt_one) hn
  -- r^N * C < ε (rearranging r^N < ε/C with C > 0)
  have h1 : corr.decay_ratio ^ N * corr.bound_const < ε :=
    (lt_div_iff₀ corr.bound_const_pos).mp hN
  -- Chain: gap(n) ≤ C·r^n ≤ C·r^N = r^N·C < ε
  nlinarith [corr.exponential_bound n, corr.bound_const_pos]

/-- The Heyting gap is ℓ¹-summable: Σ gap(n) < ∞.
    Proof: gap(n) is non-negative and bounded by C · rⁿ. The geometric
    series Σ rⁿ converges since r < 1, so Σ C·rⁿ = C/(1−r) converges.
    By the comparison test, Σ gap(n) converges. -/
theorem heyting_gap_summable (corr : SpectralHeytingCorrespondence) :
    Summable corr.heyting_gap := by
  refine Summable.of_nonneg_of_le corr.heyting_gap_nonneg corr.exponential_bound ?_
  exact (summable_geometric_of_lt_one (le_of_lt corr.decay_ratio_pos)
    corr.decay_ratio_lt_one).mul_left corr.bound_const

end HeytingLean.FractalUniverse.NucleusConnection
