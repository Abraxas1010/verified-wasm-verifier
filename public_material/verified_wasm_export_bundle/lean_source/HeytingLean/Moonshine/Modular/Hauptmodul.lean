import HeytingLean.Moonshine.Hauptmodul
import HeytingLean.Moonshine.Modular.JInvariantInvariance
import HeytingLean.Moonshine.Modular.KleinJ0LaurentExpansion
import HeytingLean.Moonshine.Modular.KleinDenominatorTailMajorant

set_option autoImplicit false

noncomputable section

namespace HeytingLean.Moonshine.Modular

open UpperHalfPlane

open scoped MatrixGroups

open Filter
open scoped Topology

/-!
## Minimal analytic-side "Hauptmodul-like" properties for `kleinJ₀`

The global genus-zero content of Borcherds is far beyond Gate A. For downstream work we only need
two practical facts about the analytic `kleinJ₀`:
- invariance under the level-1 action (`SL(2,ℤ)`),
- a normalized principal part at infinity (encoded as an explicit Laurent truncation for `Im(τ)` large).

This file packages those into a reusable predicate, and proves it for `kleinJ₀`.
-/

/-- A lightweight "principal part at infinity" package for the first few `J` coefficients. -/
def HasJTruncAtImInfty (f : ℍ → ℂ) : Prop :=
  ∃ A : ℝ, ∃ tail : ℍ → ℂ, ∀ τ : ℍ, A < τ.im →
    f τ =
      (q τ)⁻¹ + (firstJCoeff : ℂ) * (q τ)
        + (secondJCoeff : ℂ) * (q τ) ^ 2 + (q τ) ^ 3 * tail τ

/-- Invariance under a subgroup of `SL(2,ℤ)`. -/
def IsSL2ZInvariant (Γ : Subgroup SL2Z) (f : ℍ → ℂ) : Prop :=
  ∀ γ : SL2Z, γ ∈ Γ → ∀ τ : ℍ, f (γ • τ) = f τ

/-- A minimal "Hauptmodul-like" predicate: invariance + normalized principal part at infinity. -/
structure IsHauptmodulLike (Γ : Subgroup SL2Z) (f : ℍ → ℂ) : Prop where
  invariant : IsSL2ZInvariant Γ f
  jTrunc : HasJTruncAtImInfty f

/--
A strengthened package for concrete `kleinJ₀` work: `IsHauptmodulLike` plus a global
nonvanishing witness for a chosen denominator function.
-/
structure IsHauptmodulLikeWithDenom
    (Γ : Subgroup SL2Z) (f denom : ℍ → ℂ) : Prop where
  base : IsHauptmodulLike Γ f
  denom_nonvanishing : ∀ τ : ℍ, denom τ ≠ 0

/--
Minimal operational Hauptmodul predicate used in the Moonshine modular layer.

This is an alias so downstream code can use a stable name while we keep the underlying
payload explicit (invariance + normalized principal part at infinity).
-/
abbrev IsHauptmodul (Γ : Subgroup SL2Z) (f : ℍ → ℂ) : Prop :=
  IsHauptmodulLike Γ f

/-- `IsHauptmodul` plus an explicit global denominator nonvanishing witness. -/
abbrev IsHauptmodulWithDenom
    (Γ : Subgroup SL2Z) (f denom : ℍ → ℂ) : Prop :=
  IsHauptmodulLikeWithDenom Γ f denom

theorem kleinJ₀_hasJTruncAtImInfty : HasJTruncAtImInfty kleinJ₀ := by
  rcases exists_im_bound_kleinJ₀_eq_trunc with ⟨A, hA⟩
  refine ⟨A, fun τ ↦ kleinA_tail_eval (q τ), ?_⟩
  intro τ hIm
  simpa using hA τ hIm

theorem kleinJ₀_isSL2ZInvariant : IsSL2ZInvariant (⊤ : Subgroup SL2Z) kleinJ₀ := by
  intro γ _ τ
  -- `SL2Z` is definitionaly `SL(2,ℤ)` (the same group acting on `ℍ`).
  simpa [SL2Z] using (kleinJ₀_sl2_invariant (γ := γ) (τ := τ))

theorem kleinJ₀_isHauptmodulLike : IsHauptmodulLike (⊤ : Subgroup SL2Z) kleinJ₀ := by
  refine ⟨kleinJ₀_isSL2ZInvariant, kleinJ₀_hasJTruncAtImInfty⟩

theorem kleinJ₀_isHauptmodul : IsHauptmodul (⊤ : Subgroup SL2Z) kleinJ₀ :=
  kleinJ₀_isHauptmodulLike

theorem kleinJ₀_denominator_nonvanishing : ∀ τ : ℍ, kleinDenom τ ≠ 0 :=
  kleinDenom_ne_zero_global

theorem kleinJ₀_isHauptmodulLikeWithDenom :
    IsHauptmodulLikeWithDenom (⊤ : Subgroup SL2Z) kleinJ₀ kleinDenom := by
  refine ⟨kleinJ₀_isHauptmodulLike, ?_⟩
  exact kleinJ₀_denominator_nonvanishing

theorem kleinJ₀_isHauptmodulWithDenom :
    IsHauptmodulWithDenom (⊤ : Subgroup SL2Z) kleinJ₀ kleinDenom :=
  kleinJ₀_isHauptmodulLikeWithDenom

end HeytingLean.Moonshine.Modular
