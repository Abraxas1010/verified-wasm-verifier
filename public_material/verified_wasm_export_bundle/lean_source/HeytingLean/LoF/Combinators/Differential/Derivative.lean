import Mathlib.LinearAlgebra.Prod
import HeytingLean.LoF.Combinators.Differential.LinearComb

/-!
# Differential combinators: dual numbers + basic derivatives

We model “exact differentiability” using dual numbers: a value is paired with a tangent,
and application satisfies a Leibniz rule.

This file provides:
- a generic `Dual` container;
- dual-number application on `FormalSum K`;
- bundled partials of bilinear application;
- a bundled derivative for the S-denotation expressed via bilinear application;
- an “exact” (dual-number style) chain rule lemma.
-/

noncomputable section

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Differential

open scoped BigOperators

/-! ## Dual layer -/

structure Dual (V : Type*) where
  base : V
  tangent : V
deriving Repr

namespace Dual

variable {V : Type*}

instance [Add V] : Add (Dual V) :=
  ⟨fun x y => ⟨x.base + y.base, x.tangent + y.tangent⟩⟩

instance [Zero V] : Zero (Dual V) :=
  ⟨⟨0, 0⟩⟩

instance {R : Type*} [SMul R V] : SMul R (Dual V) :=
  ⟨fun r x => ⟨r • x.base, r • x.tangent⟩⟩

def pure [Zero V] (v : V) : Dual V :=
  ⟨v, 0⟩

def withTangent (base tangent : V) : Dual V :=
  ⟨base, tangent⟩

end Dual

/-! ## Dual application + derivatives on `FormalSum` -/

section FormalSumDeriv

variable {K : Type*} [CommSemiring K]

def dualApp (f x : Dual (FormalSum K)) : Dual (FormalSum K) :=
  { base := FormalSum.app (K := K) f.base x.base
    tangent :=
      FormalSum.app (K := K) f.tangent x.base +
      FormalSum.app (K := K) f.base x.tangent }

noncomputable def derivativeApp1 (x : FormalSum K) : FormalSum K →ₗ[K] FormalSum K :=
  (FormalSum.appBilin (K := K)).flip x

noncomputable def derivativeApp2 (f : FormalSum K) : FormalSum K →ₗ[K] FormalSum K :=
  (FormalSum.appBilin (K := K)) f

def K_denote (x _y : FormalSum K) : FormalSum K := x

noncomputable def K_jacobian : (FormalSum K →ₗ[K] FormalSum K) × (FormalSum K →ₗ[K] FormalSum K) :=
  (LinearMap.id, 0)

def S_denote (x y z : FormalSum K) : FormalSum K :=
  FormalSum.app (K := K) (FormalSum.app (K := K) x z) (FormalSum.app (K := K) y z)

noncomputable def S_derivative (x y z : FormalSum K) :
    (FormalSum K × (FormalSum K × FormalSum K)) →ₗ[K] FormalSum K :=
  let yz : FormalSum K := FormalSum.app (K := K) y z
  let xz : FormalSum K := FormalSum.app (K := K) x z
  let dxProj : (FormalSum K × (FormalSum K × FormalSum K)) →ₗ[K] FormalSum K :=
    LinearMap.fst K (FormalSum K) (FormalSum K × FormalSum K)
  let dyProj : (FormalSum K × (FormalSum K × FormalSum K)) →ₗ[K] FormalSum K :=
    (LinearMap.fst K (FormalSum K) (FormalSum K)).comp (LinearMap.snd K (FormalSum K) (FormalSum K × FormalSum K))
  let dzProj : (FormalSum K × (FormalSum K × FormalSum K)) →ₗ[K] FormalSum K :=
    (LinearMap.snd K (FormalSum K) (FormalSum K)).comp (LinearMap.snd K (FormalSum K) (FormalSum K × FormalSum K))
  let term_dx : (FormalSum K × (FormalSum K × FormalSum K)) →ₗ[K] FormalSum K :=
    ((derivativeApp1 (K := K) yz).comp (derivativeApp1 (K := K) z)).comp dxProj
  let term_dy : (FormalSum K × (FormalSum K × FormalSum K)) →ₗ[K] FormalSum K :=
    ((derivativeApp2 (K := K) xz).comp (derivativeApp1 (K := K) z)).comp dyProj
  let term_dz₁ : (FormalSum K × (FormalSum K × FormalSum K)) →ₗ[K] FormalSum K :=
    ((derivativeApp1 (K := K) yz).comp (derivativeApp2 (K := K) x)).comp dzProj
  let term_dz₂ : (FormalSum K × (FormalSum K × FormalSum K)) →ₗ[K] FormalSum K :=
    ((derivativeApp2 (K := K) xz).comp (derivativeApp2 (K := K) y)).comp dzProj
  term_dx + term_dy + term_dz₁ + term_dz₂

@[simp]
theorem derivativeApp1_apply (x v : FormalSum K) :
    derivativeApp1 (K := K) x v = FormalSum.app (K := K) v x := by
  -- `derivativeApp1 x` is `v ↦ v ⬝ x`.
  simp [derivativeApp1]

@[simp]
theorem derivativeApp2_apply (f x : FormalSum K) :
    derivativeApp2 (K := K) f x = FormalSum.app (K := K) f x := by
  -- `derivativeApp2 f` is `x ↦ f ⬝ x`.
  simp [derivativeApp2]

theorem dualApp_chainRule_consistent (f g x dx : FormalSum K) :
    (dualApp (K := K) (Dual.pure f)
          (dualApp (K := K) (Dual.pure g) ⟨x, dx⟩)).tangent =
      ((derivativeApp2 (K := K) f).comp (derivativeApp2 (K := K) g)) dx := by
  simp [dualApp, Dual.pure, LinearMap.comp_apply, FormalSum.app_zero_left]

theorem S_derivative_apply (x y z dx dy dz : FormalSum K) :
    (S_derivative (K := K) x y z) (dx, (dy, dz)) =
      let yz : FormalSum K := FormalSum.app (K := K) y z
      let xz : FormalSum K := FormalSum.app (K := K) x z
      (FormalSum.app (K := K) (FormalSum.app (K := K) dx z) yz) +
      (FormalSum.app (K := K) xz (FormalSum.app (K := K) dy z)) +
      (FormalSum.app (K := K) (FormalSum.app (K := K) x dz) yz) +
      (FormalSum.app (K := K) xz (FormalSum.app (K := K) y dz)) := by
  simp [S_derivative, LinearMap.comp_apply, LinearMap.add_apply]

theorem S_derivative_correct (x y z dx dy dz : FormalSum K) :
    let base := S_denote (K := K) x y z
    let tangent := (S_derivative (K := K) x y z) (dx, (dy, dz))
    dualApp (K := K)
      (dualApp (K := K) ⟨x, dx⟩ ⟨z, dz⟩)
      (dualApp (K := K) ⟨y, dy⟩ ⟨z, dz⟩) = ⟨base, tangent⟩ := by
  -- Expand the dual-number computation of `S_denote` and match it against `S_derivative`.
  simp [S_denote, dualApp, S_derivative_apply, FormalSum.app_add_left, FormalSum.app_add_right,
    add_assoc, add_left_comm, add_comm]

theorem chainRule
    {W : Type*} [AddCommMonoid W] [Module K W]
    (f : FormalSum K → W)
    (g : FormalSum K → FormalSum K)
    (Df : FormalSum K →ₗ[K] W)
    (Dg : FormalSum K →ₗ[K] FormalSum K)
    (hf : ∀ x dx, f (x + dx) = f x + Df dx)
    (hg : ∀ x dx, g (x + dx) = g x + Dg dx) :
    ∀ x dx, (f ∘ g) (x + dx) = (f ∘ g) x + (Df.comp Dg) dx := by
  intro x dx
  have hg' : g (x + dx) = g x + Dg dx := hg x dx
  calc
    (f ∘ g) (x + dx) = f (g (x + dx)) := rfl
    _ = f (g x + Dg dx) := by simp [hg']
    _ = f (g x) + Df (Dg dx) := by simpa using hf (g x) (Dg dx)
    _ = (f ∘ g) x + (Df.comp Dg) dx := by
          simp [LinearMap.comp_apply]

end FormalSumDeriv

end Differential
end Combinators
end LoF
end HeytingLean
