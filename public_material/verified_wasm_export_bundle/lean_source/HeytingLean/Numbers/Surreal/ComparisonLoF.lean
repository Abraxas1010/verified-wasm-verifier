import HeytingLean.LoF.RightLeg
import HeytingLean.LoF.RightLeg.Instances
import HeytingLean.LoF.ComparisonNucleus

/-!
# Real diamond (LoF right leg) — parametric RightLeg with default Option‑A instance
-/

namespace HeytingLean
namespace Numbers
namespace Surreal

open HeytingLean.LoF
open HeytingLean.Numbers.SurrealCore

def RL_default : HeytingLean.LoF.RightLeg (Set SurrealCore.PreGame) := HeytingLean.LoF.Default.mk

abbrev Ω_ℓ_lof := (RL_default).Ω_ℓ
abbrev Ω_comp_lof := (RL_default).Ω_comp
def f_lof := (RL_default).f
def g_lof := (RL_default).g
def gc_lof := (RL_default).gc
def R_comp_lof := (RL_default).R_comp
def factor_lof := (RL_default).factor

lemma diamond_commutes_pointwise_le (S : Set PreGame) :
  f_lof S ≤
  factor_lof ⟨ (R_comp_lof).act S, (R_comp_lof).idempotent S ⟩ :=
  RightLeg.f_le_factor_pointwise RL_default S

/-! ### Comparison CompSpec for the LoF right‑leg (default Option‑A RL) -/

open HeytingLean.LoF.Comparison

def compSpec_lof : CompSpec (Set PreGame) Ω_ℓ_lof where
  f := f_lof
  g := g_lof
  mon_f := (gc_lof).monotone_l
  mon_g := (gc_lof).monotone_u
  gc := gc_lof

/-- Strong hypothesis pack for the default RL (identity closure). -/
def strong_lof : StrongHyp (Set PreGame) Ω_ℓ_lof where
  f := f_lof
  g := g_lof
  mon_f := (gc_lof).monotone_l
  mon_g := (gc_lof).monotone_u
  gc := gc_lof
  map_inf := by
    intro x y
    -- Identify both sides extentionally inside the fixed-point lattice
    apply Subtype.ext
    -- Reduce the goal to the nucleus-level `map_inf` computation.
    have htarget :
        RL_default.R_dir (x ⊓ y) =
          RL_default.R_dir ((RL_default.R_dir x) ⊓ (RL_default.R_dir y)) := by
      calc
        RL_default.R_dir (x ⊓ y)
            = RL_default.R_dir x ⊓ RL_default.R_dir y := by
                simpa [RL_default, HeytingLean.LoF.Default.mk,
                  HeytingLean.Numbers.Surreal.R_union]
                  using (RL_default.R_dir.map_inf (x := x) (y := y))
        _ = RL_default.R_dir (RL_default.R_dir x) ⊓
              RL_default.R_dir (RL_default.R_dir y) := by
                simp [RL_default, HeytingLean.LoF.Default.mk,
                  HeytingLean.Numbers.Surreal.R_union]
        _ = RL_default.R_dir ((RL_default.R_dir x) ⊓ (RL_default.R_dir y)) := by
              simpa [RL_default, HeytingLean.LoF.Default.mk,
                HeytingLean.Numbers.Surreal.R_union]
                using (RL_default.R_dir.map_inf
                  (x := RL_default.R_dir x) (y := RL_default.R_dir y)).symm
    have hleft :
        ((f_lof (x ⊓ y) : Ω_ℓ_lof) : Set PreGame) = RL_default.R_dir (x ⊓ y) := by
      simp [f_lof, RightLeg.f, RL_default, HeytingLean.LoF.Default.mk,
        HeytingLean.Numbers.Surreal.R_union]
    have hright :
        ((f_lof x ⊓ f_lof y : Ω_ℓ_lof) : Set PreGame) =
          RL_default.R_dir ((RL_default.R_dir x) ⊓ (RL_default.R_dir y)) := by
      simpa [f_lof, RightLeg.f, RL_default, HeytingLean.LoF.Default.mk,
        HeytingLean.Numbers.Surreal.R_union]
        using (RightLeg.coe_inf (RL := RL_default) (x := f_lof x) (y := f_lof y))
    calc
      ((f_lof (x ⊓ y) : Ω_ℓ_lof) : Set PreGame)
          = RL_default.R_dir (x ⊓ y) := hleft
      _ = RL_default.R_dir ((RL_default.R_dir x) ⊓ (RL_default.R_dir y)) := htarget
      _ = ((f_lof x ⊓ f_lof y : Ω_ℓ_lof) : Set PreGame) := hright.symm

/-- Convenience: Comparison nucleus on `Set PreGame` using the strong pack. -/
def nucleus_comparison_lof : Nucleus (Set PreGame) :=
  HeytingLean.LoF.Comparison.HypPack.nucleus
    (L := Set PreGame) (Ω := Ω_ℓ_lof)
    (HeytingLean.LoF.Comparison.HypPack.strong (L := Set PreGame) (Ω := Ω_ℓ_lof) strong_lof)


end Surreal
end Numbers
end HeytingLean
