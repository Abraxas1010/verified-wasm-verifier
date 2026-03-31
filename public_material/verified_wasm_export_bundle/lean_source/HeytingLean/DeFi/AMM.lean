import Mathlib.Data.Rat.Init
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Field.Rat
import HeytingLean.DeFi.Model

/-
# DeFi.AMM

Detailed constant-product AMM model with a fee parameter and explicit
swap formulas that refine the abstract invariant in `DeFi.Model`.

This module works over rational reserves `x` and `y` and a rational fee
`fee ∈ [0, 1)`. The fee is applied to the trader's input; the effective
input that reaches the pool is `γ · Δ`, where `γ = 1 - fee`.

We provide:
* a parameter record `Params` with a fee and basic sanity bounds;
* helpers for the effective input fraction `gamma`;
* explicit X→Y and Y→X swap functions `swapX` and `swapY`;
* constant-product preservation theorems for each swap; and
* refinement lemmas showing that these swaps realise the abstract
  `Step` relation from `DeFi.Model.AMM`.
-/

namespace HeytingLean
namespace DeFi
namespace AMM

/-- AMM parameters. For now we only model a single fee parameter,
    interpreted as a fraction of input that is *taken as a fee*.

    The bounds `0 ≤ fee` and `fee < 1` ensure that the effective input
    fraction `gamma = 1 - fee` is strictly positive. -/
structure Params where
  fee : ℚ
  fee_nonneg : 0 ≤ fee
  fee_lt_one : fee < 1
  deriving Repr

/-- Effective fraction of a trade that reaches the pool. -/
def gamma (p : Params) : ℚ :=
  1 - p.fee

/-- A small helper lemma specialised to `ℚ` for constant-product
    reasoning: if `x ≠ 0` then `x * (k / x) = k`. -/
lemma mul_div_cancel_const (k x : ℚ) (hx : x ≠ 0) :
    x * (k / x) = k := by
  have hx0 : (x : ℚ) ≠ 0 := hx
  calc
    x * (k / x)
        = x * k / x := by
            -- `mul_div_assoc` gives `x * k / x = x * (k / x)`.
            simpa using (mul_div_assoc x k x).symm
    _   = k := by
            -- `mul_div_cancel_left₀` then cancels the non-zero `x`.
            simpa using (mul_div_cancel_left₀ (b := k) (a := x) hx0)

/-- Effective input that reaches the pool for an X→Y swap. -/
def effectiveInputX (p : Params) (dx : ℚ) : ℚ :=
  gamma p * dx

/-- Effective input that reaches the pool for a Y→X swap. -/
def effectiveInputY (p : Params) (dy : ℚ) : ℚ :=
  gamma p * dy

/-- Concrete X→Y swap.

The trader provides a raw input `dx` of asset X. After fees, the pool
receives `gamma p * dx`. The new X reserve is `x' = x + gamma p * dx`,
and the new Y reserve is determined by the constant-product equation
`x' * y' = k s` as `y' = k s / x'`. -/
def swapX (p : Params) (s : State) (dx : ℚ) : State :=
  let dxEff := effectiveInputX p dx
  let x' := s.x + dxEff
  { x := x'
    y := k s / x' }

/-- Concrete Y→X swap.

The trader provides a raw input `dy` of asset Y. After fees, the pool
receives `gamma p * dy`. The new Y reserve is `y' = y + gamma p * dy`,
and the new X reserve is determined by `x' = k s / y'`. -/
def swapY (p : Params) (s : State) (dy : ℚ) : State :=
  let dyEff := effectiveInputY p dy
  let y' := s.y + dyEff
  { x := k s / y'
    y := y' }

/-- Output amount of Y the trader receives in an X→Y swap. -/
def amountOutX (p : Params) (s : State) (dx : ℚ) : ℚ :=
  s.y - (swapX p s dx).y

/-- Output amount of X the trader receives in a Y→X swap. -/
def amountOutY (p : Params) (s : State) (dy : ℚ) : ℚ :=
  s.x - (swapY p s dy).x
lemma swapX_x_eq (p : Params) (s : State) (dx : ℚ) :
    (swapX p s dx).x = s.x + gamma p * dx := by
  simp [swapX, effectiveInputX, gamma, k]

lemma swapX_y_eq (p : Params) (s : State) (dx : ℚ) :
    (swapX p s dx).y = k s / (s.x + gamma p * dx) := by
  simp [swapX, effectiveInputX, gamma, k]

lemma swapY_y_eq (p : Params) (s : State) (dy : ℚ) :
    (swapY p s dy).y = s.y + gamma p * dy := by
  simp [swapY, effectiveInputY, gamma, k]

lemma swapY_x_eq (p : Params) (s : State) (dy : ℚ) :
    (swapY p s dy).x = k s / (s.y + gamma p * dy) := by
  simp [swapY, effectiveInputY, gamma, k]

/-- Constant-product preservation for an X→Y swap:
    under the abstract invariant and a non-zero post-trade X reserve,
    the concrete swap `swapX` also satisfies the invariant. -/
theorem swapX_preserves_invariant {k₀ : ℚ} (p : Params)
    (s : State) (dx : ℚ)
    (hInv : ConstantProductInvariant k₀ s)
    (hDenom : s.x + gamma p * dx ≠ 0) :
    ConstantProductInvariant k₀ (swapX p s dx) := by
  unfold ConstantProductInvariant at hInv ⊢
  -- `hInv : s.x * s.y = k₀`
  have hx' : (swapX p s dx).x = s.x + gamma p * dx := by
    simpa using swapX_x_eq p s dx
  have hx'ne : (swapX p s dx).x ≠ 0 := by
    simpa [swapX_x_eq p s dx] using hDenom
  have hprod :
      (swapX p s dx).x * (swapX p s dx).y
        = (s.x + gamma p * dx) * (k s / (s.x + gamma p * dx)) := by
    simp [swapX_x_eq, swapX_y_eq, k]
  calc
    (swapX p s dx).x * (swapX p s dx).y
        = (s.x + gamma p * dx) * (k s / (s.x + gamma p * dx)) := hprod
    _   = k s := mul_div_cancel_const (k s) (s.x + gamma p * dx) (by
            simpa using hDenom)
    _   = s.x * s.y := by
            simp [k]
    _   = k₀ := hInv

/-- Constant-product preservation for a Y→X swap:
    under the abstract invariant and a non-zero post-trade Y reserve,
    the concrete swap `swapY` also satisfies the invariant. -/
theorem swapY_preserves_invariant {k₀ : ℚ} (p : Params)
    (s : State) (dy : ℚ)
    (hInv : ConstantProductInvariant k₀ s)
    (hDenom : s.y + gamma p * dy ≠ 0) :
    ConstantProductInvariant k₀ (swapY p s dy) := by
  unfold ConstantProductInvariant at hInv ⊢
  have hy' : (swapY p s dy).y = s.y + gamma p * dy := by
    simpa using swapY_y_eq p s dy
  have hy'ne : (swapY p s dy).y ≠ 0 := by
    simpa [swapY_y_eq p s dy] using hDenom
  have hprod :
      (swapY p s dy).x * (swapY p s dy).y
        = k s / (s.y + gamma p * dy) * (s.y + gamma p * dy) := by
    simp [swapY_y_eq, swapY_x_eq, k]
  have hdenom : (s.y + gamma p * dy : ℚ) ≠ 0 := by
    simpa using hDenom
  have hcancel :
      k s / (s.y + gamma p * dy) * (s.y + gamma p * dy) = k s := by
    have h' := mul_div_cancel_const (k s) (s.y + gamma p * dy) hdenom
    simpa [mul_comm] using h'
  calc
    (swapY p s dy).x * (swapY p s dy).y
        = k s / (s.y + gamma p * dy) * (s.y + gamma p * dy) := hprod
    _   = k s := hcancel
    _   = s.x * s.y := by
            simp [k]
    _   = k₀ := hInv

/-- X→Y swap refines the abstract `Step` relation from `DeFi.Model.AMM`:
    assuming the invariant on the pre-state and a non-zero denominator,
    `swapX` realises a `Step` between the old and new states. -/
theorem swapX_refines_Step {k₀ : ℚ} (p : Params)
    (s : State) (dx : ℚ)
    (hInv : ConstantProductInvariant k₀ s)
    (hDenom : s.x + gamma p * dx ≠ 0) :
    Step k₀ s (swapX p s dx) := by
  refine And.intro ?h_pre ?h_post
  · exact hInv
  · exact swapX_preserves_invariant p s dx hInv hDenom

/-- Y→X swap refines the abstract `Step` relation from `DeFi.Model.AMM`. -/
theorem swapY_refines_Step {k₀ : ℚ} (p : Params)
    (s : State) (dy : ℚ)
    (hInv : ConstantProductInvariant k₀ s)
    (hDenom : s.y + gamma p * dy ≠ 0) :
    Step k₀ s (swapY p s dy) := by
  refine And.intro ?h_pre ?h_post
  · exact hInv
  · exact swapY_preserves_invariant p s dy hInv hDenom

/-! ### Target-reserve swaps and arbitrage states -/

/-- Input amount of X that would, in the idealised constant-product
    model with fee parameter `p`, move the AMM from state `s` to a
    post-trade state with X‑reserve exactly `x'`. This is defined
    algebraically as `(x' - s.x) / gamma p`; the hypothesis
    `gamma p ≠ 0` is required in the accompanying theorems. -/
def dxForTargetX (p : Params) (s : State) (x' : ℚ) : ℚ :=
  (x' - s.x) / gamma p

lemma swapX_dxForTargetX_x (p : Params) (s : State) (x' : ℚ)
    (hγ : gamma p ≠ 0) :
    (swapX p s (dxForTargetX p s x')).x = x' := by
  -- First show the desired equality for the X‑reserve expression.
  have hsum :
      s.x + gamma p * dxForTargetX p s x' = x' := by
    have hcancel :
        gamma p * dxForTargetX p s x'
          = (x' - s.x) :=
      mul_div_cancel_const (x' - s.x) (gamma p) hγ
    have hLhs :
        s.x + gamma p * dxForTargetX p s x'
          = s.x + (x' - s.x) := by
      -- Add `s.x` to both sides of `hcancel`.
      simpa using congrArg (fun t => s.x + t) hcancel
    calc
      s.x + gamma p * dxForTargetX p s x'
          = s.x + (x' - s.x) := hLhs
      _   = x' := by
              -- `s.x + (x' - s.x) = x'` by basic ring algebra.
              simp [sub_eq_add_neg, add_left_comm]
  calc
    (swapX p s (dxForTargetX p s x')).x
        = s.x + gamma p * dxForTargetX p s x' := by
            simpa [dxForTargetX] using
              (swapX_x_eq p s (dxForTargetX p s x'))
    _   = x' := hsum

lemma swapX_dxForTargetX_invariant {k₀ : ℚ} (p : Params)
    (s : State) (x' : ℚ)
    (hx' : x' ≠ 0)
    (hInv : ConstantProductInvariant k₀ s)
    (hγ : gamma p ≠ 0) :
    ConstantProductInvariant k₀ (swapX p s (dxForTargetX p s x')) := by
  -- Denominator non-zero follows because the post-trade X‑reserve is `x'`.
  have hx_coord :
      (swapX p s (dxForTargetX p s x')).x = x' :=
    swapX_dxForTargetX_x p s x' hγ
  have hsum :
      s.x + gamma p * dxForTargetX p s x' = x' := by
    -- Combine the coordinate formula with `swapX_x_eq`.
    have hx1 := swapX_x_eq p s (dxForTargetX p s x')
    -- hx1 : (swapX ...).x = s.x + gamma p * dxForTargetX ...
    -- hx_coord : (swapX ...).x = x'
    exact Eq.trans hx1.symm hx_coord
  have hDenom : s.x + gamma p * dxForTargetX p s x' ≠ 0 := by
    simpa [hsum] using hx'
  -- Apply the general preservation lemma for `swapX`.
  exact
    swapX_preserves_invariant p s (dxForTargetX p s x') hInv hDenom

/-! A small, spec-level arbitrage theorem: for any invariant `k₀` and
    target non-zero X‑reserve `x'`, if the pre-state `s` lies on the
    constant-product curve and we choose the concrete input
    `dxForTargetX p s x'`, then:
    * the post-state lies on the same constant-product curve;
    * its X‑reserve is exactly `x'`; and
    * by `ArbitrageOptimalityStatement` this post-state is the unique
      AMM state with invariant `k₀` and X‑reserve `x'`. -/
theorem swapX_dxForTargetX_unique_state {k₀ : ℚ} (p : Params)
    (s : State) (x' : ℚ)
    (hx' : x' ≠ 0)
    (hInv : ConstantProductInvariant k₀ s)
    (hγ : gamma p ≠ 0) :
    ConstantProductInvariant k₀ (swapX p s (dxForTargetX p s x')) ∧
    (swapX p s (dxForTargetX p s x')).x = x' ∧
    ∀ s'', ConstantProductInvariant k₀ s'' ∧ s''.x = x' →
            s'' = swapX p s (dxForTargetX p s x') := by
  -- Abbreviate the post-trade state.
  let s' := swapX p s (dxForTargetX p s x')
  have hInv' : ConstantProductInvariant k₀ s' :=
    swapX_dxForTargetX_invariant p s x' hx' hInv hγ
  have hx_coord : s'.x = x' :=
    swapX_dxForTargetX_x p s x' hγ
  -- Use the global uniqueness statement on constant-product states.
  have hex :=
    arbitrageOptimalityStatement_holds (k₀ := k₀) (x' := x') hx'
  rcases hex with ⟨s₀, hProp₀, hUnique⟩
  have hProp' : ConstantProductInvariant k₀ s' ∧ s'.x = x' :=
    And.intro hInv' hx_coord
  have h_eq : s' = s₀ := hUnique _ hProp'
  refine And.intro hInv' ?rest
  refine And.intro hx_coord ?uniq
  intro s'' hProp''
  -- Any other state with the same invariant and X‑reserve equals `s₀`,
  -- and hence equals `s'`.
  have h_to_s₀ : s'' = s₀ := hUnique _ hProp''
  simpa [s', h_eq] using h_to_s₀

end AMM
end DeFi
end HeytingLean
