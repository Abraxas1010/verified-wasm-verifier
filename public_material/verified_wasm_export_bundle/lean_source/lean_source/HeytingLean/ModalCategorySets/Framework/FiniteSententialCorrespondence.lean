import HeytingLean.ModalCategorySets.Framework.EqualityMorphismBridge
import HeytingLean.ModalCategorySets.Framework.FiniteStateFrames
import HeytingLean.ModalCategorySets.Framework.FiniteTranslation
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Embedding.Basic
import Mathlib.Tactic

namespace HeytingLean.ModalCategorySets.Framework

open scoped Classical
open HeytingLean.ModalCategorySets.Framework.Equality

universe u

inductive CardinalityLabel : Type where
  | exact (n : Nat)
  | atLeast (n : Nat)

def RealizesCardinalityLabel (α : Type u) (l : CardinalityLabel) : Prop :=
  match l with
  | .exact n => Nonempty { hα : Fintype α // @Fintype.card α hα = n }
  | .atLeast n => Nonempty { xs : Fin n → α // Function.Injective xs }

theorem nonempty_surjection_iff_card_le_of_nonempty {α β : Type u}
    [Fintype α] [Fintype β] [Nonempty β] :
    Nonempty { f : α → β // Function.Surjective f } ↔ Fintype.card β ≤ Fintype.card α := by
  constructor
  · rintro ⟨⟨f, hf⟩⟩
    exact Fintype.card_le_of_surjective f hf
  · intro h
    have hEmb : Nonempty (β ↪ α) := Function.Embedding.nonempty_of_card_le h
    rcases hEmb with ⟨e⟩
    let f : α → β := Function.invFun e
    have hf : Function.Surjective f := by
      intro b
      exact Exists.intro (e b) (Function.leftInverse_invFun e.injective b)
    exact Nonempty.intro (Subtype.mk f hf)

abbrev surjectionLineWorld (n : Nat) (i : Fin n) : Type :=
  Fin (n - i.1)

def surjectionLineLabel (n : Nat) (i : Fin n) : CardinalityLabel :=
  .exact (n - i.1)

theorem surjectionLineWorld_rel_iff {n : Nat} (i j : Fin n) :
    surjections.toKripkeCategory.toFrame.rel (surjectionLineWorld n i) (surjectionLineWorld n j) ↔
      (surjectionLineFrame n).rel i j := by
  rw [MorphismClass.toKripkeCategory_rel_iff]
  constructor
  · rintro ⟨f, hf⟩
    have hcard : n - j.1 ≤ n - i.1 := by
      simpa [surjectionLineWorld] using (Fintype.card_le_of_surjective f hf)
    have hi : i.1 < n := i.2
    have hj : j.1 < n := j.2
    have hij' : i.1 ≤ j.1 := by
      omega
    simpa [surjectionLineFrame] using hij'
  · intro hij
    have hij' : i.1 ≤ j.1 := by
      simpa [surjectionLineFrame] using hij
    have hi : i.1 < n := i.2
    have hj : j.1 < n := j.2
    have hcard : n - j.1 ≤ n - i.1 := by
      omega
    have hjPos : 0 < n - j.1 := by
      omega
    letI : Nonempty (surjectionLineWorld n j) := ⟨Fin.mk 0 hjPos⟩
    rcases (nonempty_surjection_iff_card_le_of_nonempty
      (α := surjectionLineWorld n i) (β := surjectionLineWorld n j)).2
      (by simpa [surjectionLineWorld] using hcard) with ⟨f⟩
    exact Exists.intro f.1 f.2

theorem surjectionLineWorld_realizes_label {n : Nat} (i : Fin n) :
    RealizesCardinalityLabel (surjectionLineWorld n i) (surjectionLineLabel n i) := by
  change Nonempty { hα : Fintype (Fin (n - i.1)) // @Fintype.card (Fin (n - i.1)) hα = n - i.1 }
  let hα : Fintype (Fin (n - i.1)) := inferInstance
  refine Nonempty.intro (Subtype.mk hα ?_)
  simp [hα]

theorem holds_surjectionLine_exactCardinality_iff {α : Type u} [Fintype α]
    (ρ : Valuation α) {n : Nat} (i : Fin n) :
    HoldsIn surjections ρ (exactCardinality (n - i.1)) ↔
      Fintype.card α = n - i.1 := by
  exact holds_exactCardinality_iff_fintype_card_eq (admits := surjections.admits) (ρ := ρ) _

def lollipopWitnessWorld (m : Nat) (s : LollipopState m) : Type :=
  match s with
  | .root => PEmpty
  | .cluster i =>
      if _h : i.1 < m then Fin (i.1 + 1) else Fin (m + 1)

def lollipopLabel (m : Nat) (s : LollipopState m) : CardinalityLabel :=
  match s with
  | .root => .exact 0
  | .cluster i =>
      if _h : i.1 < m then .exact (i.1 + 1) else .atLeast (m + 1)

theorem lollipopWitnessWorld_cluster_nonempty (m : Nat) (i : Fin (m + 1)) :
    Nonempty (lollipopWitnessWorld m (.cluster i)) := by
  by_cases h : i.1 < m
  · unfold lollipopWitnessWorld
    simp [h]
    exact ⟨Fin.mk 0 (Nat.succ_pos _)⟩
  · unfold lollipopWitnessWorld
    simp [h]
    exact ⟨Fin.mk 0 (Nat.succ_pos _)⟩

theorem allFunctions_rel_from_empty (β : Type u) :
    allFunctions.toKripkeCategory.toFrame.rel PEmpty β := by
  rw [MorphismClass.toKripkeCategory_rel_iff]
  exact Exists.intro PEmpty.elim trivial

theorem not_allFunctions_rel_to_empty_of_nonempty {α : Type u} [Nonempty α] :
    ¬ allFunctions.toKripkeCategory.toFrame.rel α PEmpty := by
  rw [MorphismClass.toKripkeCategory_rel_iff]
  intro h
  rcases h with ⟨f, _⟩
  rcases ‹Nonempty α› with ⟨a⟩
  exact PEmpty.elim (f a)

theorem allFunctions_rel_between_nonempty {α β : Type u} [Nonempty β] :
    allFunctions.toKripkeCategory.toFrame.rel α β := by
  rw [MorphismClass.toKripkeCategory_rel_iff]
  rcases ‹Nonempty β› with ⟨b⟩
  exact Exists.intro (fun _ => b) trivial

theorem lollipopWitnessWorld_rel_iff (m : Nat) (s t : LollipopState m) :
    allFunctions.toKripkeCategory.toFrame.rel (lollipopWitnessWorld m s) (lollipopWitnessWorld m t) ↔
      (lollipopFrame m).rel s t := by
  cases s with
  | root =>
      cases t with
      | root =>
          constructor
          · intro _
            trivial
          · intro _
            exact allFunctions_rel_from_empty PEmpty
      | cluster j =>
          constructor
          · intro _
            trivial
          · intro _
            exact allFunctions_rel_from_empty (lollipopWitnessWorld m (.cluster j))
  | cluster i =>
      cases t with
      | root =>
          letI : Nonempty (lollipopWitnessWorld m (.cluster i)) :=
            lollipopWitnessWorld_cluster_nonempty m i
          constructor
          · intro h
            exact False.elim ((not_allFunctions_rel_to_empty_of_nonempty
              (α := lollipopWitnessWorld m (.cluster i))) h)
          · intro hFalse
            exact False.elim hFalse
      | cluster j =>
          letI : Nonempty (lollipopWitnessWorld m (.cluster j)) :=
            lollipopWitnessWorld_cluster_nonempty m j
          constructor
          · intro _
            trivial
          · intro _
            exact allFunctions_rel_between_nonempty

end HeytingLean.ModalCategorySets.Framework
