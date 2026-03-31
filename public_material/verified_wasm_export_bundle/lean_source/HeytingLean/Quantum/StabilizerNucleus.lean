import Mathlib.Data.Set.Lattice
import Mathlib.Order.Nucleus
import Mathlib.Order.Sublocale
import Mathlib.Tactic

import HeytingLean.Quantum.TWA.NucleusConnection

/-!
# Stabilizer nucleus on sets (Phase 6)

This file implements a **fully provable**, purely set-algebraic “stabilizer nucleus” on
propositions about a state space.

Key idea:

* A stabilizer code on a state type `α` is specified by a family of constraints (`good g : Set α`).
* The **code space** is the intersection of all constraints:
  `codeSpace := {x | ∀ g, x ∈ good g}`.
* The associated **nucleus on propositions** (`Set α`) is the closure operator
  `U ↦ U ∪ codeSpace`.

This nucleus is inflationary, idempotent, and meet-preserving by set extensionality and `simp`.
Its fixed points are exactly the subsets containing the code space.
-/

namespace HeytingLean
namespace Quantum

universe u v

/-! ## Stabilizer code: constraints and code space -/

/-- A stabilizer code specified by a family of state constraints `good g`. -/
structure StabilizerCode (α : Type u) where
  /-- Index type for “generators / constraints”. -/
  Gen : Type v
  /-- States satisfying generator `g`. -/
  good : Gen → Set α

namespace StabilizerCode

variable {α : Type u}

/-- The code space: states satisfying all constraints. -/
def codeSpace (C : StabilizerCode α) : Set α :=
  {x | ∀ g : C.Gen, x ∈ C.good g}

@[simp] lemma mem_codeSpace (C : StabilizerCode α) (x : α) :
    x ∈ C.codeSpace ↔ ∀ g : C.Gen, x ∈ C.good g := Iff.rfl

/-- View a plain subset as a stabilizer code (single constraint). -/
def ofCodeSpace (Ω : Set α) : StabilizerCode α where
  Gen := Unit
  good := fun _ => Ω

@[simp] lemma codeSpace_ofCodeSpace (Ω : Set α) :
    (ofCodeSpace (α := α) Ω).codeSpace = Ω := by
  ext x
  simp [ofCodeSpace, codeSpace]

end StabilizerCode

/-! ## The stabilizer nucleus on propositions `Set α` -/

namespace StabilizerNucleus

variable {α : Type u}

open StabilizerCode

/-- The stabilizer nucleus on `Set α`: `U ↦ U ∪ C.codeSpace`. -/
def stabilizerNucleus (C : StabilizerCode α) : Nucleus (Set α) where
  toFun U := U ∪ C.codeSpace
  map_inf' U V := by
    simpa using (Set.inter_union_distrib_right U V C.codeSpace)
  idempotent' U := by
    intro x hx
    rcases hx with hx | hx
    · exact hx
    · exact Or.inr hx
  le_apply' U := by
    intro x hx
    exact Or.inl hx

@[simp] lemma stabilizerNucleus_apply (C : StabilizerCode α) (U : Set α) :
    stabilizerNucleus (α := α) C U = U ∪ C.codeSpace := rfl

lemma stabilizerNucleus_fixed_iff (C : StabilizerCode α) (U : Set α) :
    stabilizerNucleus (α := α) C U = U ↔ C.codeSpace ⊆ U := by
  constructor
  · intro h x hx
    have hx' : x ∈ stabilizerNucleus (α := α) C U := by
      simpa [stabilizerNucleus_apply] using (Or.inr hx : x ∈ U ∪ C.codeSpace)
    simpa [h] using hx'
  · intro hC
    ext x
    constructor
    · intro hx
      rcases hx with hxU | hxC
      · exact hxU
      · exact hC hxC
    · intro hxU
      exact Or.inl hxU

/-! ### Fixed points as the “Heyting core” -/

/-- The stabilizer “core” sublocale (fixed points of the stabilizer nucleus). -/
abbrev Core (C : StabilizerCode α) : Type u :=
  (stabilizerNucleus (α := α) C).toSublocale

@[simp] lemma mem_Core_iff_contains (C : StabilizerCode α) (U : Set α) :
    U ∈ (stabilizerNucleus (α := α) C).toSublocale ↔ C.codeSpace ⊆ U := by
  constructor
  · intro hU
    rcases (Nucleus.mem_toSublocale).1 hU with ⟨V, hV⟩
    intro x hx
    have hx' : x ∈ stabilizerNucleus (α := α) C V := by
      simpa [stabilizerNucleus_apply] using (Or.inr hx : x ∈ V ∪ C.codeSpace)
    simpa [hV] using hx'
  · intro hC
    have hfix : stabilizerNucleus (α := α) C U = U :=
      (stabilizerNucleus_fixed_iff (α := α) C U).2 hC
    exact (Nucleus.mem_toSublocale).2 ⟨U, hfix⟩

@[simp] lemma mem_codeSpaceSet_iff_contains (C : StabilizerCode α) (U : Set α) :
    U ∈ HeytingLean.Quantum.TWA.codeSpaceSet (stabilizerNucleus (α := α) C) ↔ C.codeSpace ⊆ U := by
  simp [HeytingLean.Quantum.TWA.codeSpaceSet, stabilizerNucleus_apply]

lemma codeSpace_mem_Core (C : StabilizerCode α) : C.codeSpace ∈ (stabilizerNucleus (α := α) C).toSublocale :=
  (mem_Core_iff_contains (α := α) C C.codeSpace).2 subset_rfl

lemma bot_val_eq_codeSpace (C : StabilizerCode α) :
    ((⊥ : Core (α := α) C) : Set α) = C.codeSpace := by
  -- In the fixed-point core, every element contains `C.codeSpace`, so it is the least element.
  apply le_antisymm
  · -- `⊥` is below the element `C.codeSpace` (viewed in the core).
    have hmem : C.codeSpace ∈ (stabilizerNucleus (α := α) C).toSublocale := codeSpace_mem_Core (α := α) C
    have h : (⊥ : Core (α := α) C) ≤ (⟨C.codeSpace, hmem⟩ : Core (α := α) C) := bot_le
    exact h
  · -- `C.codeSpace ⊆ (⊥ : Core C)` because `(⊥ : Core C)` is itself in the core.
    exact (mem_Core_iff_contains (α := α) C ((⊥ : Core (α := α) C) : Set α)).1 (show ((⊥ : Core (α := α) C) : Set α) ∈ _ from (⊥ : Core (α := α) C).property)

end StabilizerNucleus

end Quantum
end HeytingLean
