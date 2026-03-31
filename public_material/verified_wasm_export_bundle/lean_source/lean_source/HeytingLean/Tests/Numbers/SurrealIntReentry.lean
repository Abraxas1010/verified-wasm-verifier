import HeytingLean.Numbers.Surreal.Nucleus
import HeytingLean.Numbers.Surreal.ReentryAdapter
import HeytingLean.Generative.IntNucleusKit

open HeytingLean
open HeytingLean.Numbers.Surreal
open HeytingLean.LoF
open HeytingLean.Generative

/-!
Sanity checks for Surreal interior re-entry and IntNucleusKit.
-/

-- The carrier type for this re-entry is `Set PreGame`.
variable (S T : Set HeytingLean.Numbers.SurrealCore.PreGame)

-- Re-exported interior nucleus
abbrev R := HeytingLean.Numbers.Surreal.surrealIntReentry

#check R

-- Core properties hold by construction
example : (R).nucleus.act S ≤ S := by
  exact (R).nucleus.apply_le S

example : (R).nucleus.act ((R).nucleus.act S) = (R).nucleus.act S := by
  exact (R).nucleus.idempotent S

example : (R).nucleus.act (S ⊓ T) = (R).nucleus.act S ⊓ (R).nucleus.act T := by
  exact (R).nucleus.map_inf S T

-- IntNucleusKit helpers are available
example : IntNucleusKit.ioccam (R := (R)) S = (R).nucleus.act S := rfl

/-! ### Additional smoke checks: `ibirth` and a fixed-point set -/

-- `ibirth` is bounded by 1 for any input by idempotence
example : IntNucleusKit.ibirth (R := (R)) S ≤ 1 :=
  IntNucleusKit.ibirth_le_one (R := (R)) (a := S)

-- The canonical legal core `C` is a fixed point: `I C = C`, hence `ibirth = 0`.
example : IntNucleusKit.ibirth (R := (R)) (a := HeytingLean.Numbers.Surreal.Int.C) = 0 := by
  -- Show `R Surreal.Int.C = Surreal.Int.C`.
  have hI : HeytingLean.Numbers.Surreal.Int.I HeytingLean.Numbers.Surreal.Int.C =
      HeytingLean.Numbers.Surreal.Int.C := by
    simpa [HeytingLean.Numbers.Surreal.Int.I]
  have hfix : (R) HeytingLean.Numbers.Surreal.Int.C =
      HeytingLean.Numbers.Surreal.Int.C := by
    change HeytingLean.Numbers.Surreal.Int.I HeytingLean.Numbers.Surreal.Int.C =
      HeytingLean.Numbers.Surreal.Int.C
    simpa using hI
  exact IntNucleusKit.ibirth_eq_zero_of_fixed (R := (R))
    (a := HeytingLean.Numbers.Surreal.Int.C) hfix
