import HeytingLean.Moonshine.Modular.KleinCuspLaurentBridge
import HeytingLean.Moonshine.Modular.FundamentalDomainQBounds

import Mathlib.Analysis.Normed.Ring.InfiniteSum

set_option autoImplicit false

noncomputable section

namespace HeytingLean.Moonshine.Modular

open scoped BigOperators

/-!
## Explicit Nonvanishing for `kleinBfunExt` on a Small Disk

For `τ ∈ ModularGroup.fd` we have the explicit bound `‖q τ‖ ≤ 1/100`.
This file turns that into a usable nonvanishing lemma for the Klein denominator:
it suffices to show `kleinBfunExt q ≠ 0` for `‖q‖ ≤ 1/100`.

This is a "Gate A4" deliverable: it removes the remaining nonvanishing obstruction
for defining `kleinJ` as a holomorphic function on `ℍ`.
-/

lemma kleinBfunExt_eq_tsum_psTerm_kleinBps (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    kleinBfunExt q = ∑' n : ℕ, psTerm kleinBps q n := by
  -- Start from the `q`-expansion of the denominator `kleinDfun`.
  have hD : kleinDfun q = ∑' n : ℕ, psTerm kleinDps q n := by
    simpa [kleinDfun, kleinDps] using (kleinD_cusp_eq_tsum_kleinDSeries (q := q) hq)
  -- Shift the series and factor out `q`.
  have hshift :
      (∑' n : ℕ, psTerm kleinDps q n) = (∑' n : ℕ, psTerm kleinBps q n) * q := by
    simpa [kleinDps, kleinBps] using (tsum_psTerm_kleinDSeries_eq_tsum_kleinBSeries_mul_q (q := q) hq)
  -- Use `kleinDfun = q * kleinBfunExt` away from `0` and cancel the nonzero `q`.
  have hmul : kleinDfun q = q * kleinBfunExt q := kleinDfun_eq_mul_kleinBfunExt (q := q) hq0
  -- Multiply by `q⁻¹` on the left to cancel.
  have : kleinBfunExt q = q⁻¹ * kleinDfun q := by
    -- `q⁻¹ * (q * kleinBfunExt q) = kleinBfunExt q`.
    calc
      kleinBfunExt q = q⁻¹ * (q * kleinBfunExt q) := by simp [hq0]
      _ = q⁻¹ * kleinDfun q := by simp [hmul]
  -- Rewrite `kleinDfun q` as a `tsum` and simplify.
  calc
    kleinBfunExt q = q⁻¹ * kleinDfun q := this
    _ = q⁻¹ * ((∑' n : ℕ, psTerm kleinBps q n) * q) := by
          simp [hD, hshift]
    _ = ∑' n : ℕ, psTerm kleinBps q n := by
          ring_nf
          simp [hq0]

end HeytingLean.Moonshine.Modular
