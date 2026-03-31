import HeytingLean.ModalCategorySets.Validities.ControlCore
import Mathlib.Data.Fintype.Powerset

namespace HeytingLean.ModalCategorySets.Validities

open HeytingLean.ModalCategorySets.Propositional

universe u v

namespace BooleanFrames

/-- The finite Boolean-frame on `n` generators, ordered by subset inclusion. -/
def frame (n : Nat) : Frame (Finset (Fin n)) where
  rel s t := s ⊆ t

/-- Shift a Boolean-frame valuation so that truth at `u` in the shifted model matches
truth at `s ∪ u` in the original model. -/
def shiftVal {α : Type v} {n : Nat}
    (s : Finset (Fin n)) (val : Finset (Fin n) → α → Prop) :
    Finset (Fin n) → α → Prop :=
  fun u p => val (s ∪ u) p

theorem frame_reflexive (n : Nat) :
    Reflexive (frame n) := by
  intro s x hx
  exact hx

theorem frame_transitive (n : Nat) :
    Transitive (frame n) := by
  intro s t u hst htu
  exact Set.Subset.trans hst htu

theorem frame_directed (n : Nat) :
    ∀ s t u, (frame n).rel s t → (frame n).rel s u →
      ∃ z, (frame n).rel t z ∧ (frame n).rel u z := by
  intro s t u hst hsu
  refine Exists.intro (t ∪ u) ?_
  constructor
  · intro x hx
    exact Finset.mem_union.mpr (Or.inl hx)
  · intro x hx
    exact Finset.mem_union.mpr (Or.inr hx)

theorem validatesGrzDot2Core (n : Nat) :
    ValidatesGrzDot2Core (frame n) := by
  letI : Fintype (Finset (Fin n)) := inferInstance
  letI : Finite (Finset (Fin n)) := inferInstance
  intro α p
  refine And.intro
    (axiomT_valid_of_reflexive (F := frame n) (frame_reflexive n) p)
    (And.intro
      (axiom4_valid_of_transitive (F := frame n) (frame_transitive n) p)
      (And.intro
        (axiomDot2_valid_of_directed (F := frame n) (frame_directed n) p)
        ?_))
  change Frame.Valid (OrderedFrames.orderFrame (Finset (Fin n))) (axiomGrz p)
  exact OrderedFrames.axiomGrz_valid_on_finite_partialOrder (W := Finset (Fin n)) p

theorem satisfies_shiftVal_iff {α : Type v} {n : Nat}
    (s u : Finset (Fin n)) (val : Finset (Fin n) → α → Prop) (φ : Formula α) :
    let M : Model (Finset (Fin n)) α := mkModel (frame n) val
    let M' : Model (Finset (Fin n)) α := mkModel (frame n) (shiftVal s val)
    satisfies M (s ∪ u) φ ↔ satisfies M' u φ := by
  intro M M'
  induction φ generalizing u with
  | var p =>
      rfl
  | bot =>
      rfl
  | imp φ ψ ihφ ihψ =>
      constructor
      · intro h hφ
        exact (ihψ u).1 (h ((ihφ u).2 hφ))
      · intro h hφ
        exact (ihψ u).2 (h ((ihφ u).1 hφ))
  | conj φ ψ ihφ ihψ =>
      constructor
      · rintro ⟨hφ, hψ⟩
        exact And.intro ((ihφ u).1 hφ) ((ihψ u).1 hψ)
      · rintro ⟨hφ, hψ⟩
        exact And.intro ((ihφ u).2 hφ) ((ihψ u).2 hψ)
  | disj φ ψ ihφ ihψ =>
      constructor
      · intro h
        rcases h with hφ | hψ
        · exact Or.inl ((ihφ u).1 hφ)
        · exact Or.inr ((ihψ u).1 hψ)
      · intro h
        rcases h with hφ | hψ
        · exact Or.inl ((ihφ u).2 hφ)
        · exact Or.inr ((ihψ u).2 hψ)
  | box φ ih =>
      constructor
      · intro h v huv
        have hrel : s ∪ u ⊆ s ∪ v := by
          intro x hx
          rcases Finset.mem_union.mp hx with hx | hx
          · exact Finset.mem_union.mpr (Or.inl hx)
          · exact Finset.mem_union.mpr (Or.inr (huv hx))
        exact (ih v).1 (h (s ∪ v) hrel)
      · intro h v huv
        have hu_v : u ⊆ v := by
          intro x hx
          exact huv (Finset.mem_union.mpr (Or.inr hx))
        have hs_v : s ⊆ v := by
          intro x hx
          exact huv (Finset.mem_union.mpr (Or.inl hx))
        have hStep : satisfies (mkModel (frame n) (shiftVal s val)) v φ :=
          h v hu_v
        have hBack : satisfies (mkModel (frame n) val) (s ∪ v) φ :=
          (ih v).2 hStep
        have hEq : s ∪ v = v := Finset.union_eq_right.mpr hs_v
        simpa [hEq] using hBack
  | dia φ ih =>
      constructor
      · rintro ⟨v, huv, hφ⟩
        have hu_v : u ⊆ v := by
          intro x hx
          exact huv (Finset.mem_union.mpr (Or.inr hx))
        have hs_v : s ⊆ v := by
          intro x hx
          exact huv (Finset.mem_union.mpr (Or.inl hx))
        have hEq : s ∪ v = v := Finset.union_eq_right.mpr hs_v
        have hShift : satisfies (mkModel (frame n) (shiftVal s val)) v φ := by
          exact (ih v).1 (by simpa [hEq] using hφ)
        exact Exists.intro v (And.intro hu_v hShift)
      · rintro ⟨v, huv, hφ⟩
        refine Exists.intro (s ∪ v) ?_
        refine And.intro ?_ ?_
        · intro x hx
          rcases Finset.mem_union.mp hx with hx | hx
          · exact Finset.mem_union.mpr (Or.inl hx)
          · exact Finset.mem_union.mpr (Or.inr (huv hx))
        · exact (ih v).2 hφ

/-- Pointed validity at the initial Boolean world `∅`. -/
def ValidAtBottom {α : Type v} (n : Nat) (φ : Formula α) : Prop :=
  ∀ val, satisfies (mkModel (frame n) val) ∅ φ

theorem valid_iff_validAtBottom {α : Type v} {n : Nat} {φ : Formula α} :
    (frame n).Valid φ ↔ ValidAtBottom n φ := by
  constructor
  · intro hValid val
    exact hValid val ∅
  · intro hBottom val s
    let val' : Finset (Fin n) → α → Prop := shiftVal s val
    have hRoot : satisfies (mkModel (frame n) val') ∅ φ := hBottom val'
    have hShift :
        satisfies (mkModel (frame n) val) (s ∪ ∅) φ ↔
          satisfies (mkModel (frame n) val') ∅ φ :=
      satisfies_shiftVal_iff s ∅ val φ
    simpa using hShift.mpr hRoot

/-- Semantic benchmark class for arbitrary formulas: validity on every finite Boolean frame. -/
def ValidOnAllFiniteBooleanFrames {α : Type v} (φ : Formula α) : Prop :=
  ∀ n, Frame.Valid (frame n) φ

theorem validOnAllFiniteBooleanFrames_iff_validAtBottom {α : Type v} {φ : Formula α} :
    ValidOnAllFiniteBooleanFrames φ ↔ ∀ n, ValidAtBottom n φ := by
  constructor
  · intro hValid n
    exact (valid_iff_validAtBottom (n := n) (φ := φ)).1 (hValid n)
  · intro hValid n
    exact (valid_iff_validAtBottom (n := n) (φ := φ)).2 (hValid n)

theorem validOnAllFiniteBooleanFrames_of_axiomT {α : Type v} (p : α) :
    ValidOnAllFiniteBooleanFrames (axiomT p) := by
  intro n
  exact (validatesGrzDot2Core n p).1

theorem validOnAllFiniteBooleanFrames_of_axiom4 {α : Type v} (p : α) :
    ValidOnAllFiniteBooleanFrames (axiom4 p) := by
  intro n
  exact (validatesGrzDot2Core n p).2.1

theorem validOnAllFiniteBooleanFrames_of_axiomDot2 {α : Type v} (p : α) :
    ValidOnAllFiniteBooleanFrames (axiomDot2 p) := by
  intro n
  exact (validatesGrzDot2Core n p).2.2.1

theorem validOnAllFiniteBooleanFrames_of_axiomGrz {α : Type v} (p : α) :
    ValidOnAllFiniteBooleanFrames (axiomGrz p) := by
  intro n
  exact (validatesGrzDot2Core n p).2.2.2

end BooleanFrames

end HeytingLean.ModalCategorySets.Validities
