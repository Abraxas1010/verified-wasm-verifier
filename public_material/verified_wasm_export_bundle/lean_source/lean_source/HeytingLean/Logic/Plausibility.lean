import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import HeytingLean.LoF.HeytingCore
import HeytingLean.Logic.ResiduatedLadder

/-
  Plausibility layer atop the re-entry nucleus core.

  This module provides:
  * A lightweight residuated scale structure (`ResiduatedScale`) capturing a
    combination operator and its residual (adjoint) with a mild `y ≠ ⊤`
    side-condition, suitable for numeric plausibility values.
  * A concrete instance on `ℝ≥0∞` using multiplication and the usual division
    residual (`residualMul`).
  * A plausibility measure on the fixed-point core `Ω_R`, monotone with respect
    to the Heyting order and compatible with meet/implication.
  * A dimension-indexed family of re-entry nuclei with monotone cores.
  * A `ClassicalFragment` predicate marking where double negation collapses.
-/

namespace HeytingLean
namespace Logic

open HeytingLean.LoF

/-- A residuated scale packages a combination operator `combine` (think: numeric
product) and its residual `resid` (right adjoint) with an adjunction that holds
whenever the right argument is not `⊤`. -/
structure ResiduatedScale (V : Type*) [Preorder V] [Top V] where
  combine : V → V → V
  unit    : V
  resid   : V → V → V
  residuation : ∀ {x y z}, y ≠ (⊤ : V) → (combine x y ≤ z ↔ x ≤ resid y z)

namespace ResiduatedScale

variable {V : Type*} [Preorder V] [Top V] (S : ResiduatedScale V)

end ResiduatedScale

/-- Numeric residual for multiplication on `ENNReal`. -/
noncomputable def residualMul (q r : ENNReal) : ENNReal :=
  if _ : q = 0 then (⊤ : ENNReal) else q⁻¹ * r

lemma residualMul_residuation {x q z : ENNReal} (hq_top : q ≠ (⊤ : ENNReal)) :
    x * q ≤ z ↔ x ≤ residualMul q z := by
  classical
  by_cases hq0 : q = 0
  · -- Degenerate case: `q = 0` makes the left inequality trivial.
    subst hq0
    simp [residualMul]
  · -- Proper case: use the `mul_le_iff_le_inv` adjunction for `ℝ≥0∞`.
    have h := ENNReal.mul_le_iff_le_inv (a := x) (b := z) (r := q) hq0 hq_top
    -- The lemma is stated as `q * x ≤ z ↔ x ≤ q⁻¹ * z`; commute the product.
    simpa [residualMul, hq0, mul_comm] using h

/-- When `q ≠ 0`, the residual coincides with division. -/
lemma residualMul_eq_div {q r : ENNReal} (hq0 : q ≠ 0) :
    residualMul q r = r / q := by
  classical
  simp [residualMul, hq0, div_eq_mul_inv, mul_comm]

/-- Residuated scale on extended nonnegative reals with multiplication. -/
noncomputable def ennrealScale : ResiduatedScale ENNReal where
  combine := fun x y => x * y
  unit := 1
  resid := residualMul
  residuation := by
    intro x y z
    exact residualMul_residuation (x := x) (q := y) (z := z)

/-- Plausibility measure on the Heyting core `Ω_R` valued in a residuated scale.
This is the quantitative face of the “dimensional limit” story: monotone on
fixed points, multiplicative on meets, and upper-bounded by the residual on
implication, ready to specialize to the Cox/Jaynes regime. -/
structure PlausibilityMeasure {α : Type u} [PrimaryAlgebra α]
    (R : Reentry α) {V : Type v} [Preorder V] [Top V]
    (S : ResiduatedScale V) where
  μ        : R.Omega → V
  monotone : Monotone μ
  μ_top    : μ (⊤ : R.Omega) = S.unit
  μ_inf    : ∀ a b, μ (a ⊓ b) = S.combine (μ a) (μ b)
  μ_imp_le : ∀ a b, μ (a ⇨ b) ≤ S.resid (μ a) (μ b)

@[simp] lemma PlausibilityMeasure.mu_top {α : Type u} [PrimaryAlgebra α]
    {V : Type v} [Preorder V] [Top V] {R : Reentry α} {S : ResiduatedScale V}
    (μ : PlausibilityMeasure (R := R) (S := S)) :
    μ.μ (⊤ : R.Omega) = S.unit :=
  μ.μ_top

namespace PlausibilityMeasure

variable {α : Type u} [PrimaryAlgebra α]
variable {V : Type v} [Preorder V] [Top V]
variable {R : Reentry α} {S : ResiduatedScale V}
(μ : PlausibilityMeasure (R := R) (S := S))

lemma inf_eval (a b : R.Omega) :
    μ.μ (a ⊓ b) = S.combine (μ.μ a) (μ.μ b) :=
  μ.μ_inf a b

lemma himp_upper (a b : R.Omega) :
    μ.μ (a ⇨ b) ≤ S.resid (μ.μ a) (μ.μ b) :=
  μ.μ_imp_le a b

lemma deduction_bound {a b c : R.Omega} :
    a ⊓ b ≤ c → S.combine (μ.μ a) (μ.μ b) ≤ μ.μ c := by
  intro h
  have hμ := μ.monotone h
  simpa [μ.inf_eval] using hμ

end PlausibilityMeasure

/-- A strengthened plausibility measure where implication matches the scale residual.
In the classical window this recovers Bayes’ rule as “residual = division”. -/
structure StrictPlausibilityMeasure {α : Type u} [PrimaryAlgebra α]
    (R : Reentry α) {V : Type v} [Preorder V] [Top V]
    (S : ResiduatedScale V) extends PlausibilityMeasure (R := R) (S := S) where
  μ_imp_eq : ∀ a b, μ (a ⇨ b) = S.resid (μ a) (μ b)

@[simp] lemma StrictPlausibilityMeasure.mu_imp_eq {α : Type u} [PrimaryAlgebra α]
    {V : Type v} [Preorder V] [Top V] {R : Reentry α} {S : ResiduatedScale V}
    (μ : StrictPlausibilityMeasure (R := R) (S := S)) (a b : R.Omega) :
    μ.toPlausibilityMeasure.μ (a ⇨ b) = S.resid (μ.toPlausibilityMeasure.μ a) (μ.toPlausibilityMeasure.μ b) :=
  μ.μ_imp_eq a b

namespace StrictPlausibilityMeasure

variable {α : Type u} [PrimaryAlgebra α]
variable {V : Type v} [Preorder V] [Top V]
variable {R : Reentry α} {S : ResiduatedScale V}
(μ : StrictPlausibilityMeasure (R := R) (S := S))

lemma himp_eval (a b : R.Omega) :
    μ.toPlausibilityMeasure.μ (a ⇨ b) =
      S.resid (μ.toPlausibilityMeasure.μ a) (μ.toPlausibilityMeasure.μ b) :=
  μ.mu_imp_eq a b

end StrictPlausibilityMeasure

/-- Bayes-style division for ENNReal-valued strict measures when the divisor is nonzero. -/
lemma StrictPlausibilityMeasure.himp_div {α : Type u} [PrimaryAlgebra α]
    {R : Reentry α}
    (μ : StrictPlausibilityMeasure (R := R) (S := ennrealScale))
    {a b : R.Omega} (ha : μ.toPlausibilityMeasure.μ a ≠ 0) :
    μ.toPlausibilityMeasure.μ (a ⇨ b) =
      μ.toPlausibilityMeasure.μ b / μ.toPlausibilityMeasure.μ a := by
  have h := μ.mu_imp_eq a b
  -- Use the numeric residual lemma.
  have hdiv := residualMul_eq_div (q := μ.toPlausibilityMeasure.μ a)
    (r := μ.toPlausibilityMeasure.μ b) ha
  simpa [ennrealScale, h] using hdiv

/-- Trivial one-point scale on `PUnit`, useful for degenerate instances/tests. -/
def punitScale : ResiduatedScale PUnit where
  combine := fun _ _ => PUnit.unit
  unit := PUnit.unit
  resid := fun _ _ => PUnit.unit
  residuation := by
    intro x y z hy
    constructor <;> intro _ <;> trivial

/-- Strict plausibility measure collapsing everything to the trivial scale. -/
def trivialStrictMeasure {α : Type u} [PrimaryAlgebra α] (R : Reentry α) :
    StrictPlausibilityMeasure (R := R) (S := punitScale) where
  μ := fun _ => PUnit.unit
  monotone := by intro a b h; trivial
  μ_top := rfl
  μ_inf := by intro a b; rfl
  μ_imp_le := by intro a b; trivial
  μ_imp_eq := by intro a b; rfl

/-- Dimension-indexed re-entry family with weakening (`R_{d+1} ≤ R_d`). -/
structure DimensionFamily (α : Type u) [PrimaryAlgebra α] where
  R : ℕ → Reentry α
  weakening : ∀ d x, (R (d+1)) x ≤ (R d) x

namespace DimensionFamily

variable {α : Type u} [PrimaryAlgebra α] (F : DimensionFamily α)

/-- Inclusion of fixed-point cores `Ω_d ⊆ Ω_{d+1}` induced by weakening. -/
def omegaInclusion (d : ℕ) : (F.R d).Omega → (F.R (d+1)).Omega :=
  fun a =>
    let x : α := a
    have hx_fix : (F.R d) x = x := Reentry.Omega.apply_coe (R := F.R d) a
    have hle : (F.R (d+1)) x ≤ x := by
      have h := F.weakening d x
      simpa [hx_fix] using h
    have hge : x ≤ (F.R (d+1)) x := Reentry.le_apply (R := F.R (d+1)) x
    have hfix : (F.R (d+1)) x = x := le_antisymm hle hge
    Reentry.Omega.mk (R := F.R (d+1)) x hfix

lemma omegaInclusion_coe (d : ℕ) (a : (F.R d).Omega) :
    ((F.omegaInclusion d a : (F.R (d+1)).Omega) : α) = (a : α) := rfl

end DimensionFamily

/-- Elements where double negation collapses (Boolean window). -/
def ClassicalFragment {α : Type u} [PrimaryAlgebra α] (R : Reentry α) :
    Set R.Omega :=
  fun a => ((a ⇨ (⊥ : R.Omega)) ⇨ (⊥ : R.Omega)) = a

end Logic
end HeytingLean
