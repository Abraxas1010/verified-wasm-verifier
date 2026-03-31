import Mathlib
import HeytingLean.Core.Nucleus
import HeytingLean.BST.Foundation

/-!
# BST.Bridge.Nucleus

Actual bounded-carrier nucleus for the BST foundation.

The carrier is a `BoundedFinset`, and the lattice elements are bounded finitary
subsets of that carrier. A generator slice induces a genuine nucleus by closing
each bounded subset under union with those generators.
-/

namespace HeytingLean.BST.Bridge

open HeytingLean.Core

abbrev CarrierSlice {U : UniverseBound} {α : Type*} [DecidableEq α]
    (carrier : BoundedFinset U α) :=
  { s : Finset α // s ⊆ (carrier : Finset α) }

namespace CarrierSlice

variable {U : UniverseBound} {α : Type*} [DecidableEq α] {carrier : BoundedFinset U α}

instance : CoeOut (CarrierSlice carrier) (Finset α) := ⟨Subtype.val⟩

@[simp] theorem subset_carrier (s : CarrierSlice carrier) :
    (s : Finset α) ⊆ (carrier : Finset α) :=
  s.2

def whole (carrier : BoundedFinset U α) : CarrierSlice carrier :=
  ⟨carrier, by intro x hx; exact hx⟩

def empty (carrier : BoundedFinset U α) : CarrierSlice carrier :=
  ⟨∅, by simp⟩

def ofFinset? (carrier : BoundedFinset U α) (s : Finset α) : Option (CarrierSlice carrier) :=
  if h : s ⊆ (carrier : Finset α) then some ⟨s, h⟩ else none

def toBoundedFinset (s : CarrierSlice carrier) : BoundedFinset U α :=
  ⟨s, le_trans (Finset.card_le_card s.2) carrier.2⟩

instance : LE (CarrierSlice carrier) := ⟨fun s t => (s : Finset α) ⊆ (t : Finset α)⟩

instance : PartialOrder (CarrierSlice carrier) where
  le := (· ≤ ·)
  le_refl s := by intro x hx; exact hx
  le_trans _ _ _ hst htu := by intro x hx; exact htu (hst hx)
  le_antisymm s t hst hts := by
    apply Subtype.ext
    exact Finset.Subset.antisymm hst hts

instance : SemilatticeInf (CarrierSlice carrier) where
  inf s t := ⟨(s : Finset α) ∩ (t : Finset α), by
    intro x hx
    exact s.2 (by simpa using Finset.mem_of_mem_inter_left hx)⟩
  inf_le_left s t := by
    intro x hx
    exact Finset.mem_of_mem_inter_left hx
  inf_le_right s t := by
    intro x hx
    exact Finset.mem_of_mem_inter_right hx
  le_inf s t u hst hsu := by
    intro x hx
    exact Finset.mem_inter.mpr ⟨hst hx, hsu hx⟩

instance : OrderBot (CarrierSlice carrier) where
  bot := empty carrier
  bot_le s := by
    intro x hx
    simp [empty] at hx

end CarrierSlice

variable {U : UniverseBound} {α : Type*} [DecidableEq α] {carrier : BoundedFinset U α}

def generatedNucleus (gens : CarrierSlice carrier) : Core.Nucleus (CarrierSlice carrier) where
  R s := ⟨(s : Finset α) ∪ (gens : Finset α), Finset.union_subset s.2 gens.2⟩
  extensive := by
    intro s x hx
    exact Finset.mem_union.mpr (Or.inl hx)
  idempotent := by
    intro s
    apply Subtype.ext
    ext x
    simp [Finset.mem_union]
  meet_preserving := by
    intro s t
    apply Subtype.ext
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hxg
      · rcases Finset.mem_inter.mp hx with ⟨hs, ht⟩
        exact Finset.mem_inter.mpr
          ⟨Finset.mem_union.mpr (Or.inl hs), Finset.mem_union.mpr (Or.inl ht)⟩
      · exact Finset.mem_inter.mpr
          ⟨Finset.mem_union.mpr (Or.inr hxg), Finset.mem_union.mpr (Or.inr hxg)⟩
    · intro hx
      rcases Finset.mem_inter.mp hx with ⟨hs, ht⟩
      rcases Finset.mem_union.mp hs with hs | hxg
      · rcases Finset.mem_union.mp ht with ht | hxg
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hs, ht⟩))
        · exact Finset.mem_union.mpr (Or.inr hxg)
      · exact Finset.mem_union.mpr (Or.inr hxg)

theorem mem_fixedPoints_iff {gens : CarrierSlice carrier} {s : CarrierSlice carrier} :
    s ∈ (generatedNucleus gens).fixedPoints ↔ gens ≤ s := by
  constructor
  · intro hs x hx
    have hs' : (generatedNucleus gens).R s = s := by
      simpa [Core.Nucleus.fixedPoints] using hs
    have hx' : x ∈ ((generatedNucleus gens).R s : Finset α) := Finset.mem_union.mpr (Or.inr hx)
    simpa [hs'] using hx'
  · intro h
    change (generatedNucleus gens).R s = s
    apply Subtype.ext
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact hx
      · exact h hx
    · intro hx
      exact Finset.mem_union.mpr (Or.inl hx)

end HeytingLean.BST.Bridge
