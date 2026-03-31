import HeytingLean.ModalCategorySets.Propositional.Axioms
import HeytingLean.ModalCategorySets.Validities.BooleanFrames
import HeytingLean.ModalCategorySets.Validities.FiniteLatticeCharacterization
import HeytingLean.ModalCategorySets.Validities.S4Universal

namespace HeytingLean.ModalCategorySets.Propositional

open HeytingLean.ModalCategorySets.Validities

universe u

/-- A modal theory presented semantically as a class of formulas. -/
abbrev FormulaTheory (α : Type u) := Formula α → Prop

/-- The fragment of modal theories currently realized in the codebase. -/
inductive ModalTheory : Type where
  | K
  | S4
  | S5
  | Triv

/-- Frame-level validity predicate for the currently implemented modal theories. -/
def ModalTheory.Validates {W : Type u} (F : Frame W) : ModalTheory → Prop
  | .K => ∀ {α : Type u} (p q : α), F.Valid (axiomK p q)
  | .S4 => ∀ {α : Type u} (p : α), F.Valid (axiomT p) ∧ F.Valid (axiom4 p)
  | .S5 => ∀ {α : Type u} (p : α), F.Valid (axiomT p) ∧ F.Valid (axiom4 p) ∧ F.Valid (axiom5 p)
  | .Triv => ∀ {α : Type u} (p : α), F.Valid (axiomTriv p)

theorem validatesK {W : Type u} (F : Frame W) :
    ModalTheory.Validates F .K := by
  intro α p q
  exact axiomK_valid F p q

theorem validatesTriv_of_identityRelation {W : Type u} (F : Frame W)
    (hId : IsIdentityRelation F) :
    ModalTheory.Validates F .Triv := by
  intro α p
  exact axiomTriv_valid_of_identityRelation hId p

namespace FormulaTheory

/-- The semantic `Grz.2` surface used in the modal-category-of-sets development:
the formulas valid on all finite Boolean frames. -/
def Grz2 {α : Type u} : FormulaTheory α :=
  BooleanFrames.ValidOnAllFiniteBooleanFrames

/-- Equivalent finite-semilattice presentation of `Grz.2`: truth at the bottom world
of every finite join-semilattice with bottom. -/
def Grz2FiniteJoinSemilattice {α : Type u} : FormulaTheory α :=
  FiniteLatticeCharacterization.ValidAtBottomAllFiniteJoinSemilattices

theorem grz2_iff_validOnAllFiniteBooleanFrames {α : Type u} {φ : Formula α} :
    Grz2 φ ↔ BooleanFrames.ValidOnAllFiniteBooleanFrames φ :=
  Iff.rfl

theorem grz2_iff_validAtBottomAllFiniteJoinSemilattices {α : Type u} {φ : Formula α} :
    Grz2 φ ↔ Grz2FiniteJoinSemilattice φ :=
  FiniteLatticeCharacterization.validOnAllFiniteBooleanFrames_iff_validAtBottom

theorem grz2_of_axiomT {α : Type u} (p : α) :
    Grz2 (axiomT p) :=
  BooleanFrames.validOnAllFiniteBooleanFrames_of_axiomT p

theorem grz2_of_axiom4 {α : Type u} (p : α) :
    Grz2 (axiom4 p) :=
  BooleanFrames.validOnAllFiniteBooleanFrames_of_axiom4 p

theorem grz2_of_axiomDot2 {α : Type u} (p : α) :
    Grz2 (axiomDot2 p) :=
  BooleanFrames.validOnAllFiniteBooleanFrames_of_axiomDot2 p

theorem grz2_of_axiomGrz {α : Type u} (p : α) :
    Grz2 (axiomGrz p) :=
  BooleanFrames.validOnAllFiniteBooleanFrames_of_axiomGrz p

end FormulaTheory

end HeytingLean.ModalCategorySets.Propositional
