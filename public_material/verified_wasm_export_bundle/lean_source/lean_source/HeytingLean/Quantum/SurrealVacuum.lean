import Mathlib.Data.Set.Lattice
import HeytingLean.Numbers.SurrealCore
import HeytingLean.Quantum.SurrealOML
import HeytingLean.Quantum.VacuumOmegaR
import HeytingLean.Quantum.Translate.Core
import HeytingLean.Quantum.Translate.Modality
import HeytingLean.Numbers.Surreal.ReentryLoF

/-
# Surreal vacuum proposition and quantum translation

This module defines:

* a surreal vacuum proposition in the OML carrier `Surrealβ`,
  taken to be the singleton containing the Conway null cut, and
* a quantum translation `surrealQLMap : QLMap Surrealβ Surrealβ`
  whose modality is induced from the surreal reentry nucleus.

These are the ingredients needed to instantiate `VacuumOmegaRContext`
for surreals in Direction 6.
-/

namespace HeytingLean
namespace Quantum
namespace Surreal

open HeytingLean.Numbers
open HeytingLean.Numbers.SurrealCore
open HeytingLean.Quantum
open HeytingLean.Quantum.SurrealOML
open HeytingLean.Quantum.Translate
open Set

abbrev β := Surrealβ
abbrev α := Surrealβ

/-! ### Surreal vacuum proposition -/

/-- Surreal vacuum set: singleton containing the Conway null cut. -/
def surrealVacuumSet : β := nullCutSet

/-- Surreal vacuum witness on the orthomodular carrier `β`. -/
noncomputable def surrealVacuumWitness : VacuumWitness β :=
  { vacuum := surrealVacuumSet
    nontrivial := by
      -- `nullCutSet` is non-bottom (`bot_ne_nullCutSet`).
      intro hbot
      have : nullCut ∈ (⊥ : β) := by
        have : nullCut ∈ surrealVacuumSet := by
          simp [surrealVacuumSet, nullCutSet]
        simpa [hbot, SurrealOML.bot_eq_empty] using this
      simpa [SurrealOML.bot_eq_empty] using this }

/-! ### Surreal quantum translation QLMap -/

/-- Surreal QLMap: identity translation on `β` with modality induced
from the surreal reentry nucleus. -/
noncomputable def surrealQLMap : QLMap β α := by
  classical
  refine
    { M := Reentry.toQuantumModality (R := Numbers.Surreal.surrealReentry)
      tr := id
      map_inf := ?_
      map_sup_le := ?_ }
  · -- The induced modality is identity for `surrealReentry`.
    intro x y
    simp [Reentry.toQuantumModality, Numbers.Surreal.surrealReentry,
      Modality.close, Modality.idNucleus]
  · -- Subadditivity is reflexive under identity closure.
    intro x y
    simp [Reentry.toQuantumModality, Numbers.Surreal.surrealReentry,
      Modality.close, Modality.idNucleus]

/-! ### Surreal VacuumOmegaRContext and Euler bridge -/

/-- Concrete surreal `VacuumOmegaRContext` on `β := Set PreGame` and
`α := Set PreGame`, using the identity translation and reentry nucleus,
with vacuum proposition the null-cut singleton. -/
noncomputable def surrealVacuumContext :
    VacuumOmegaRContext β α := by
  classical
  refine
    { F := surrealQLMap
      R := Numbers.Surreal.surrealReentry
      modality_agrees := ?_
      vacuum := surrealVacuumWitness
      vacuum_primordial := ?_ }
  · -- Compatibility: the modality kernel is exactly the surreal
    -- reentry nucleus (both are the identity on `Set PreGame`).
    intro S
    simp [surrealQLMap, Numbers.Surreal.surrealReentry,
      Reentry.toQuantumModality, Modality.close,
      Modality.idNucleus]
  · -- Closing the image of the vacuum under the modality yields the
    -- primordial fixed point of the surreal reentry nucleus.
    -- Here both sides are definitionally `nullCutSet`.
    simp [surrealQLMap, surrealVacuumSet, surrealVacuumWitness,
      Numbers.Surreal.surrealReentry, Reentry.toQuantumModality,
      Modality.close, Modality.idNucleus]

/-! ### Specialised surreal equivalence statements -/

/-- In the surreal instantiation, the Ωᴿ-level vacuum equals the Euler
boundary of the surreal reentry nucleus. -/
lemma surreal_vacuum_eq_euler :
    surrealVacuumContext.vacuumOmega
      = surrealVacuumContext.R.eulerBoundary :=
  surrealVacuumContext.vacuumOmega_eq_eulerBoundary

/-- In the surreal instantiation, the Ωᴿ-level vacuum has Euler/Occam
birthday zero in the `LoF.Reentry` sense. This is a direct
specialisation of `vacuumOmega_birth_zero`. -/
lemma surreal_vacuum_birth_zero :
    Epistemic.birth surrealVacuumContext.R
      (((surrealVacuumContext.vacuumOmega :
          surrealVacuumContext.R.Omega) : α)) = 0 :=
  surrealVacuumContext.vacuumOmega_birth_zero

/-- Underlying carrier of the surreal Ωᴿ vacuum is exactly the
singleton null-cut set. -/
lemma surreal_vacuum_support_eq_nullCutSet :
    ((surrealVacuumContext.vacuumOmega :
        surrealVacuumContext.R.Omega) : α)
      = surrealVacuumSet := by
  classical
  -- Use the generic `vacuumOmega_coe` lemma together with the facts
  -- that `tr := id` and the modality is induced from the identity
  -- nucleus.
  have h := VacuumOmegaRContext.vacuumOmega_coe (C := surrealVacuumContext)
  -- Unfold the right-hand side and simplify.
  -- `F.tr` is `id`, and `F.M.close` is the identity closure.
  simpa [surrealVacuumContext, surrealQLMap, surrealVacuumSet,
    surrealVacuumWitness, Numbers.Surreal.surrealReentry,
    Reentry.toQuantumModality, VacuumOmegaRContext.vacuumProp,
    Modality.close, Modality.idNucleus] using h

/-- Every surreal pre-game in the Ωᴿ vacuum support has Conway
birthday zero (is definitionally the null cut). -/
lemma surreal_vacuum_elements_birth_zero (g : PreGame)
    (hg : g ∈ ((surrealVacuumContext.vacuumOmega :
        surrealVacuumContext.R.Omega) : α)) :
    birthday g = 0 := by
  classical
  -- Rewrite membership in terms of `surrealVacuumSet = nullCutSet`.
  have hg' : g ∈ surrealVacuumSet := by
    simpa [surreal_vacuum_support_eq_nullCutSet] using hg
  have hg_eq : g = nullCut := by
    simpa [surrealVacuumSet, nullCutSet] using hg'
  -- Birthday is preserved under definitional equality.
  simpa [SurrealCore.birthday, SurrealCore.nullCut, hg_eq]

/-- Occam/LoF and Conway birthdays agree for the surreal Ωᴿ vacuum:
both return zero. -/
lemma surreal_vacuum_births_agree :
    Epistemic.birth surrealVacuumContext.R
      (((surrealVacuumContext.vacuumOmega :
          surrealVacuumContext.R.Omega) : α))
      = birthday nullCut := by
  -- Left-hand side is zero by `surreal_vacuum_birth_zero`; rewrite
  -- `birthday nullCut` to the same numeral.
  simpa [SurrealCore.birthday, SurrealCore.nullCut] using
    surreal_vacuum_birth_zero

end Surreal
end Quantum
end HeytingLean
