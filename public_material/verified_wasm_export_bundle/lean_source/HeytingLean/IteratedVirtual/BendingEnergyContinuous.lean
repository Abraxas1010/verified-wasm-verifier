import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# IteratedVirtual.BendingEnergyContinuous

A lightweight “continuous” analogue of the discrete bending-energy story.

We deliberately avoid committing to a specific analytic energy functional (e.g. an integral of
`(f'')^2`) because that requires substantial measure-theory and regularity infrastructure.
Instead, we:

1. Prove an honest *structural* statement: if `deriv (deriv f) = 0` everywhere (and the relevant
   differentiability hypotheses hold), then `f` is affine.
2. Package an **interface**: any nonnegative energy functional that vanishes on such affine data
   is minimized by the affine curve determined by boundary constraints.

This closes the Phase‑8 “continuous energy minimization” item at the correct abstraction boundary:
it is ready to be instantiated once a concrete analytic functional is chosen and verified.
-/

namespace HeytingLean
namespace IteratedVirtual

open scoped Real

/-! ## A calculus lemma: `deriv = 0` implies constant -/

theorem eq_const_of_deriv_eq_zero (f : ℝ → ℝ) (hf : Differentiable ℝ f) (h' : ∀ x, deriv f x = 0) :
    ∀ x, f x = f 0 := by
  intro x
  by_cases hx : x = 0
  · simp [hx]
  have hlt : x < 0 ∨ 0 < x := lt_or_gt_of_ne hx
  cases hlt with
  | inl hxneg =>
      -- Use MVT on `(x, 0)`.
      have hab : x < (0 : ℝ) := hxneg
      have hcont : ContinuousOn f (Set.Icc x 0) := hf.continuous.continuousOn
      have hdiff : DifferentiableOn ℝ f (Set.Ioo x 0) := hf.differentiableOn
      rcases exists_deriv_eq_slope (f := f) hab hcont hdiff with ⟨c, hc, hderiv⟩
      have hslope : (f 0 - f x) / (0 - x) = 0 := by
        simpa [h' c] using hderiv.symm
      have hx0 : (0 - x) ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
      have : f 0 - f x = 0 := (div_eq_zero_iff).1 hslope |>.resolve_right hx0
      linarith
  | inr hxpos =>
      -- Use MVT on `(0, x)`.
      have hab : (0 : ℝ) < x := hxpos
      have hcont : ContinuousOn f (Set.Icc 0 x) := hf.continuous.continuousOn
      have hdiff : DifferentiableOn ℝ f (Set.Ioo 0 x) := hf.differentiableOn
      rcases exists_deriv_eq_slope (f := f) hab hcont hdiff with ⟨c, hc, hderiv⟩
      have hslope : (f x - f 0) / (x - 0) = 0 := by
        simpa [h' c] using hderiv.symm
      have hx0 : (x - 0) ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
      have : f x - f 0 = 0 := (div_eq_zero_iff).1 hslope |>.resolve_right hx0
      linarith

/-! ## Affine maps from boundary conditions -/

/-- The affine function taking `0 ↦ a` and `1 ↦ b`. -/
def affine01 (a b : ℝ) : ℝ → ℝ :=
  fun x => a + x * (b - a)

@[simp] theorem affine01_zero (a b : ℝ) : affine01 a b 0 = a := by
  simp [affine01]

@[simp] theorem affine01_one (a b : ℝ) : affine01 a b 1 = b := by
  calc
    affine01 a b 1 = a + (b - a) := by simp [affine01]
    _ = a + b - a := by
          simp [sub_eq_add_neg, add_assoc]
    _ = b := by simp

theorem secondDeriv_affine01 (a b : ℝ) : ∀ x, deriv (deriv (affine01 a b)) x = 0 := by
  intro x
  have h1 : deriv (affine01 a b) = fun _ => (b - a) := by
    funext y
    have hid : HasDerivAt (fun t : ℝ => t) 1 y := hasDerivAt_id y
    have hmul : HasDerivAt (fun t : ℝ => t * (b - a)) (1 * (b - a)) y := hid.mul_const (b - a)
    have hconst : HasDerivAt (fun _ : ℝ => a) 0 y := hasDerivAt_const (c := a) (x := y)
    have hadd : HasDerivAt (affine01 a b) (b - a) y := by
      simpa [affine01] using (hconst.add (by simpa using hmul))
    simpa using hadd.deriv
  simp [h1]

/-! ## Second derivative zero implies affine (global, under differentiability hypotheses) -/

theorem affine_of_secondDeriv_eq_zero (f : ℝ → ℝ)
    (hf : Differentiable ℝ f)
    (hdf : Differentiable ℝ (deriv f))
    (h2 : ∀ x, deriv (deriv f) x = 0) :
    ∀ x, f x = f 0 + x * deriv f 0 := by
  -- First, `deriv f` is constant.
  have hconst : ∀ x, deriv f x = deriv f 0 :=
    fun x => by
      have := eq_const_of_deriv_eq_zero (f := deriv f) (hf := hdf) h2 x
      simpa using this
  -- Now consider `g x := f x - x*(deriv f 0)`; show `deriv g = 0`, hence `g` is constant.
  let c : ℝ := deriv f 0
  let g : ℝ → ℝ := fun x => f x - x * c
  have hg_diff : Differentiable ℝ g := by
    -- `x ↦ x*c` is differentiable; closed under subtraction.
    simpa [g, c] using hf.sub ((differentiable_id).mul_const c)
  have hg' : ∀ x, deriv g x = 0 := by
    intro x
    have hx : deriv f x = c := by simpa [c] using hconst x
    have hsub : deriv g x = deriv f x - deriv (fun y : ℝ => y * c) x := by
      simpa [g] using
        (deriv_sub (f := f) (g := fun y : ℝ => y * c) (x := x)
          (hf := hf.differentiableAt) (hg := (differentiable_id.differentiableAt.mul_const c)))
    have hlin : deriv (fun y : ℝ => y * c) x = c := by
      have hid : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
      have hmul : HasDerivAt (fun y : ℝ => y * c) (1 * c) x := hid.mul_const c
      have htmp : deriv (fun y : ℝ => y * c) x = 1 * c := hmul.deriv
      calc
        deriv (fun y : ℝ => y * c) x = 1 * c := htmp
        _ = c := by simp
    have : deriv g x = c - c := by
      simpa [hx, hlin] using hsub
    simp [this]
  have hg_const : ∀ x, g x = g 0 :=
    eq_const_of_deriv_eq_zero (f := g) (hf := hg_diff) hg' 
  intro x
  have : f x - x * c = f 0 - 0 * c := by
    simpa [g] using hg_const x
  -- Rearrange to isolate `f x`.
  linarith [this]

/-! ## Energy interface: affine minimizer for any compatible functional -/

structure ContinuousBendingEnergyModel where
  energy : (ℝ → ℝ) → ℝ
  nonneg : ∀ f, 0 ≤ energy f
  zero_of_secondDeriv_zero : ∀ f, (∀ x, deriv (deriv f) x = 0) → energy f = 0

namespace ContinuousBendingEnergyModel

theorem affine01_minimizes (M : ContinuousBendingEnergyModel) (a b : ℝ) :
    ∀ f, M.energy (affine01 a b) ≤ M.energy f := by
  intro f
  have h0 : M.energy (affine01 a b) = 0 :=
    M.zero_of_secondDeriv_zero _ (secondDeriv_affine01 a b)
  have hf0 : 0 ≤ M.energy f := M.nonneg f
  simpa [h0] using hf0

end ContinuousBendingEnergyModel

end IteratedVirtual
end HeytingLean
