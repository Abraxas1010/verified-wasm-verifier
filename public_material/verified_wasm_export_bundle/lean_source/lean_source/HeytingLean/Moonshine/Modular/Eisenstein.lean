import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.HahnSeries.PowerSeries

set_option autoImplicit false

noncomputable section

namespace HeytingLean.Moonshine.Modular

open UpperHalfPlane

open scoped CongruenceSubgroup

local instance : NeZero (1 : ℕ) := ⟨Nat.one_ne_zero⟩

/-- Normalized level-1 Eisenstein modular form of weight 4. -/
noncomputable def E4 : ModularForm Γ(1) 4 :=
  ModularForm.E (k := 4) (by decide)

/-- Normalized level-1 Eisenstein modular form of weight 6. -/
noncomputable def E6 : ModularForm Γ(1) 6 :=
  ModularForm.E (k := 6) (by decide)

/-- `q`-expansion of a level-1 modular form, as a `PowerSeries`. -/
noncomputable def qExpansion₁ {k : ℤ} (f : ModularForm Γ(1) k) : PowerSeries ℂ :=
  ModularFormClass.qExpansion 1 f

/-- The same `q`-expansion, embedded as a Hahn/Laurent series with integer exponents. -/
noncomputable def qExpansion₁Laurent {k : ℤ} (f : ModularForm Γ(1) k) : HahnSeries ℤ ℂ :=
  HahnSeries.ofPowerSeries ℤ ℂ (qExpansion₁ f)

lemma hasSum_qExpansion₁ {k : ℤ} (f : ModularForm Γ(1) k) (τ : ℍ) :
    HasSum (fun m : ℕ ↦ (qExpansion₁ f).coeff m • (Function.Periodic.qParam 1 τ) ^ m) (f τ) := by
  simpa [qExpansion₁] using (ModularFormClass.hasSum_qExpansion (n := 1) (f := f) τ)

lemma hasSum_qExpansion₁_cusp {k : ℤ} (f : ModularForm Γ(1) k) {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun m : ℕ ↦ (qExpansion₁ f).coeff m • q ^ m)
      (SlashInvariantFormClass.cuspFunction 1 f q) := by
  simpa [qExpansion₁] using
    (ModularFormClass.hasSum_qExpansion_of_abs_lt (n := 1) (f := f) hq)

end HeytingLean.Moonshine.Modular
