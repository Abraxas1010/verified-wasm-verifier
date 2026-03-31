import Mathlib.Data.Set.Lattice
import HeytingLean.LoF.Nucleus
import HeytingLean.Quantum.VacuumOmegaR
import HeytingLean.Quantum.QGINucleus
import HeytingLean.Quantum.OML.Examples.QGIInterferometer

/-
Concrete QGI-flavoured context layered on top of the abstract
`VacuumOmegaRContext`.

Design:
* Use `β := QGIβ` from `QGIInterferometer` as the OML carrier.
* Use `α := Set β` as a simple configuration lattice.
* Keep an arbitrary `VacuumOmegaRContext β α` as the Ωᴿ kernel.
* Add a `QGINucleus α` capturing a minimal non-bottom stable configuration
  interpreted as the QGI vacuum-support set.
* Add a deliberately coarse `QLMap` from β into α that sends all
  propositions to the same support set, just enough to satisfy the bridge
  hypothesis in
  `VacuumOmegaRContext`.

This provides a concrete, QGI-motivated context without altering the core
`LoF.Reentry` axioms. More refined translations can be plugged in later.
-/

namespace HeytingLean
namespace Quantum
namespace QGIContext

open LoF
open Quantum
open Quantum.OML
open Quantum.OML.QGIInterferometer
open Set

universe u

/-- OML carrier for the QGI context. -/
abbrev β := QGIβ

/-- Ambient carrier for the QGI context: a simple configuration lattice. -/
abbrev α := Set β

/-- Primary algebra instance for `Set β`, via the existing frame structure. -/
noncomputable instance instPrimaryAlgebraSetQGI : PrimaryAlgebra (Set β) :=
  { toFrame := inferInstance }

/-- Minimal QGI interior nucleus on `Set β`.

For now this is just the identity interior with support = `{labPath}`;
it is enough to witness a minimal non-bottom stable configuration. -/
noncomputable def qgiInterior : QGINucleus (Set β) := by
  classical
  refine
    { act := id
      monotone := ?_
      idempotent := ?_
      apply_le := ?_
      map_inf := ?_
      support := {b | b = labPath}
      support_mem := ?_
      support_nonbot := ?_ }
  · intro a b hab; simpa using hab
  · intro a; rfl
  · intro a; exact le_rfl
  · intro a b; rfl
  · rfl
  · -- `{labPath}` is non-bottom.
    refine bot_lt_iff_ne_bot.mpr ?_
    intro h
    have hmem : labPath ∈ ({b : β | b = labPath} : Set β) := by simp
    simp [h] at hmem

/-! ### Coarse QGI translation layer -/

/-- Identity nucleus on `Set β`, viewed through the `Modality` wrapper. -/
noncomputable def idModalitySetQGI : Quantum.Translate.Modality (Set β) :=
  { J := Quantum.Translate.Modality.idNucleus (Set β)
    preserves_top := by
      -- For the identity nucleus, closing `⊤` yields `⊤`.
      rfl }

/-- A coarse QGI translation: send every β-proposition to the support set.

This is intentionally simple; it is only used to witness the existence of
some `QLMap` whose modality aligns with a re-entry nucleus in a concrete
context. More refined translations can be added later. -/
noncomputable def qgiQLMap : Quantum.Translate.QLMap β (Set β) := by
  classical
  refine
    { M := idModalitySetQGI
      tr := fun _ => {b | b = labPath}
      map_inf := ?_
      map_sup_le := ?_ }
  · intro x y
    -- Images are constant; the closure of their meet equals the singleton.
    simp [Quantum.Translate.Modality.close, idModalitySetQGI]
  · intro x y
    -- The closed join is again the same singleton, which trivially
    -- contains the image of `x ⊔ y` under this constant map.
    simp [Quantum.Translate.Modality.close, idModalitySetQGI]

/-- A minimal concrete `VacuumWitness` on the QGI OML, taking `labPath` as the
    distinguished non-bottom proposition. -/
noncomputable def vacuum_qgi : VacuumWitness β :=
  { vacuum := labPath
    nontrivial := by
      -- In the `H2` lattice, `X ≠ ⊥`.
      decide }

/-- Re-entry nucleus on `Set β` for the concrete QGI context, using the identity
    nucleus and a minimal support window concentrated at `labPath`. -/
noncomputable def reentryQGI : LoF.Reentry (Set β) := by
  classical
  refine
    { nucleus := (⊥ : Nucleus (Set β))
      primordial := {b : β | b = labPath}
      counter := {b : β | b = freePath}
      support := {b : β | b = labPath}
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
  · rfl
  · -- `{labPath}` is non-bottom.
    refine bot_lt_iff_ne_bot.mpr ?_
    intro h
    have hmem : labPath ∈ ({b : β | b = labPath} : Set β) := by simp
    simp [h] at hmem
  · -- `{freePath}` is non-bottom.
    refine bot_lt_iff_ne_bot.mpr ?_
    intro h
    have hmem : freePath ∈ ({b : β | b = freePath} : Set β) := by simp
    simp [h] at hmem
  · -- The singleton supports are disjoint.
    ext i
    constructor
    · intro hi
      rcases hi with ⟨h0, h1⟩
      cases h0
      cases h1
    · intro hi; cases hi
  · -- `primordial` lies inside the support window (it is equal to it).
    exact le_rfl
  · -- The bottom nucleus is the identity on `Set β`.
    simp
  · -- Minimality: any non-bottom fixed point inside the support contains `labPath`.
    intro x _hx_fix hx_pos hx_sup
    have hx_ne : x ≠ (⊥ : Set β) := bot_lt_iff_ne_bot.mp hx_pos
    have hx_nonempty : x.Nonempty :=
      Set.nonempty_iff_ne_empty.mpr (by simpa using hx_ne)
    obtain ⟨w, hw⟩ := hx_nonempty
    have hw_lab : w = labPath := by
      have := hx_sup hw
      simpa using this
    have hx_lab : labPath ∈ x := by simpa [hw_lab] using hw
    intro b hb
    have hb_lab : b = labPath := by
      simpa using hb
    subst hb_lab
    simpa using hx_lab

/-- Base Ωᴿ context for the QGI example, using the identity re-entry on
    `Set β` and the constant QLMap sending all propositions to the lab-path
    support set. -/
noncomputable def qgiBaseContext : VacuumOmegaRContext β (Set β) := by
  classical
  refine
    { F := qgiQLMap
      R := reentryQGI
      modality_agrees := ?_
      vacuum := vacuum_qgi
      vacuum_primordial := ?_ }
  · intro a
    -- Both modalities are definitionally the identity nucleus.
    rfl
  · -- Closing the image of the vacuum under the identity modality returns
    -- the singleton `{labPath}`, which is exactly `reentryQGI.primordial`.
    simp [qgiQLMap, idModalitySetQGI, reentryQGI,
      Quantum.Translate.Modality.close,
      vacuum_qgi]

/-- Composite QGI context data: a base Ωᴿ context together with a QGI interior
    nucleus and coarse translation, all over the same carriers. -/
structure Bundle where
  (base    : VacuumOmegaRContext β (Set β))
  (nucleus : QGINucleus (Set β))
  (Fqgi    : Quantum.Translate.QLMap β (Set β))

/-- Default composite QGI context, bundling the base Ωᴿ context, interior
    nucleus, and coarse translation map for the QGI example. -/
noncomputable def default : Bundle :=
  { base    := qgiBaseContext
    nucleus := qgiInterior
    Fqgi    := qgiQLMap }

end QGIContext
end Quantum
end HeytingLean
