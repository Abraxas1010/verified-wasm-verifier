import HeytingLean.LoF.Nucleus
import HeytingLean.Numbers.SurrealCore
import HeytingLean.Numbers.Surreal.Nucleus
import HeytingLean.Quantum.SurrealOML
import HeytingLean.Quantum.Translate.Modality

/-
# Surreal LoF-style reentry nucleus (identity)

This module equips the carrier `Set SurrealCore.PreGame` with a
`LoF.Reentry` structure using the identity nucleus. The primordial
fixed point is the singleton set containing the Conway null cut
`{∅ ∣ ∅}`, and the counter-process is its Boolean complement.

The nucleus is mathematically simple (closure = identity) but satisfies
all `Reentry` axioms exactly, with a clean minimality proof based on
the fact that the singleton is the least non-bottom subset in the
powerset lattice.
-/

namespace HeytingLean
namespace Numbers
namespace Surreal

open HeytingLean.LoF
open HeytingLean.Numbers.SurrealCore
open HeytingLean.Quantum
open HeytingLean.Quantum.SurrealOML
open Set

abbrev Carrier := Set PreGame

/-- Surreal reentry nucleus on `Set PreGame`, using the identity closure and
the null-cut singleton as the primordial fixed point. -/
noncomputable def surrealReentry : Reentry Carrier := by
  classical
  -- Identity nucleus on the powerset lattice.
  let N : Nucleus Carrier := Quantum.Translate.Modality.idNucleus Carrier
  -- Primordial core: singleton containing the Conway null cut.
  let C : Carrier := nullCutSet
  refine
    { nucleus := N
      primordial := C
      counter := Cᶜ
      support := C
      primordial_mem := ?_
      counter_mem := ?_
      primordial_nonbot := ?_
      counter_nonbot := ?_
      orthogonal := ?_
      primordial_in_support := ?_
      map_bot := ?_
      primordial_minimal := ?_ }
  · -- Identity nucleus fixes every set.
    rfl
  · -- Identity nucleus fixes every set.
    rfl
  · -- `{nullCut}` is non-bottom.
    have hne : (C : Carrier) ≠ ⊥ := by
      intro h
      have : nullCut ∈ (⊥ : Carrier) := by
        have : nullCut ∈ C := by
          simp [C, nullCutSet]
        simpa [h] using this
      simpa [SurrealOML.bot_eq_empty] using this
    exact lt_of_le_of_ne bot_le hne.symm
  · -- The complement of `{nullCut}` is non-bottom.
    have hne : (Cᶜ : Carrier) ≠ (⊥ : Carrier) :=
      SurrealOML.compl_nullCutSet_ne_bot
    exact lt_of_le_of_ne bot_le hne.symm
  · -- Orthogonality: core and its complement meet in bottom.
    simpa [C] using SurrealOML.inf_compl_nullCutSet
  · -- The primordial core equals the support window.
    exact le_rfl
  · -- Identity nucleus fixes bottom.
    rfl
  · -- Minimality: any nontrivial fixed point inside the support window
    -- must coincide with the singleton `C`, hence must contain `C`.
    intro x _hx_fix hx_pos hx_sup
    -- `⊥ < x` implies `x ≠ ⊥`.
    have hne : (x : Carrier) ≠ (⊥ : Carrier) :=
      (bot_lt_iff_ne_bot.mp hx_pos)
    -- Any non-bottom subset of a singleton must equal the singleton.
    have hsubset : (x : Carrier) ⊆ C := hx_sup
    have hnonempty : (x : Carrier).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr (by
        -- Rewrite `⊥` as `∅` in the surreal carrier.
        have hbot : (⊥ : Carrier) = (∅ : Carrier) := by
          simpa using (SurrealOML.bot_eq_empty : (⊥ : Surrealβ) = (∅ : Set PreGame))
        simpa [hbot] using hne)
    -- Extract a witness `g ∈ x` and show it must be `nullCut`.
    rcases hnonempty with ⟨g, hgx⟩
    have hgC : g ∈ C := hsubset hgx
    have hg_eq : g = nullCut := by
      -- `C` is exactly `{g | g = nullCut}`.
      simpa [C, nullCutSet] using hgC
    -- Show that `x` contains `nullCut`.
    have hnull_in_x : nullCut ∈ x := by
      simpa [hg_eq] using hgx
    -- Finally, prove `C ≤ x`.
    intro g hgC'
    have hg_eq' : g = nullCut := by
      simpa [C, nullCutSet] using hgC'
    simpa [hg_eq'] using hnull_in_x

end Surreal
end Numbers
end HeytingLean
