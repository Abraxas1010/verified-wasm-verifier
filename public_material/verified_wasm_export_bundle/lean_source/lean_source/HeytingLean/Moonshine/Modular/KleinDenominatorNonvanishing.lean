import HeytingLean.Moonshine.Modular.KleinCuspLaurentBridge
import HeytingLean.Moonshine.Modular.KleinCuspFunction
import HeytingLean.Moonshine.Modular.QParam

set_option autoImplicit false

noncomputable section

namespace HeytingLean.Moonshine.Modular

open UpperHalfPlane

open Filter
open scoped Topology

/-!
## Nonvanishing of the Klein denominator for large `Im(τ)`

The classical identity is `(E4 τ)^3 - (E6 τ)^2 = 1728 * Δ(τ)`, which implies global nonvanishing
on `ℍ` since `Δ(τ) = η(τ)^24` and `η` is nonzero. At present we only need (and can prove with the
current local Taylor infrastructure) a weaker but kernel-pure statement:

For `Im(τ)` sufficiently large, the denominator is nonzero.

This is enough to justify local Laurent expansions at infinity and is the next stepping stone
toward a full global proof via the discriminant identity.
-/

lemma exists_im_bound_kleinDenom_ne_zero :
    ∃ A : ℝ, ∀ τ : ℍ, A < τ.im → (E4 τ) ^ 3 - (E6 τ) ^ 2 ≠ 0 := by
  -- Extract a ball around `0` on which `kleinBfunExt` is nonzero.
  rcases (Metric.eventually_nhds_iff_ball).1 eventually_ne_zero_kleinBfunExt with ⟨ε, hεpos, hε⟩
  -- Choose an imaginary-part bound forcing `‖q τ‖ < ε`.
  rcases exists_im_bound_norm_q_lt ε hεpos with ⟨A, hA⟩
  refine ⟨A, ?_⟩
  intro τ hIm
  have hq0 : q τ ≠ 0 := q_ne_zero τ
  have hball : q τ ∈ Metric.ball (0 : ℂ) ε := by
    have : ‖q τ‖ < ε := hA τ hIm
    simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using this
  have hB : kleinBfunExt (q τ) ≠ 0 := hε (q τ) hball
  have hD : kleinDfun (q τ) ≠ 0 := by
    -- `kleinDfun q = q * kleinBfunExt q` away from `0`.
    have hmul : kleinDfun (q τ) = q τ * kleinBfunExt (q τ) :=
      kleinDfun_eq_mul_kleinBfunExt (q := q τ) hq0
    have : q τ * kleinBfunExt (q τ) ≠ 0 := mul_ne_zero hq0 hB
    simpa [hmul] using this
  -- Transfer from cusp coordinate back to `τ`.
  simpa [q, kleinDfun, E4_eq_E4_cusp (τ := τ), E6_eq_E6_cusp (τ := τ)] using hD

end HeytingLean.Moonshine.Modular

