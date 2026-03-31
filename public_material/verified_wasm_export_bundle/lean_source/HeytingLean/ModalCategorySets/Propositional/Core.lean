import HeytingLean.Logics.Modal.Kripke

namespace HeytingLean.ModalCategorySets.Propositional

open HeytingLean.Logics.Modal

universe u v

abbrev Formula := HeytingLean.Logics.Modal.Formula
abbrev Frame (W : Type u) := HeytingLean.Logics.Modal.Frame W
abbrev Model (W : Type u) (α : Type v) := HeytingLean.Logics.Modal.Model W α
def satisfies {W : Type u} {α : Type v} (M : Model W α) :
    W → Formula α → Prop :=
  HeytingLean.Logics.Modal.satisfies M

namespace Formula

variable {α : Type v}

/-- Negation as implication into bottom. -/
def neg (φ : Formula α) : Formula α := .imp φ .bot

/-- The always-true formula. -/
def top : Formula α := neg .bot

/-- Biconditional as conjunction of both implications. -/
def iff (φ ψ : Formula α) : Formula α := .conj (.imp φ ψ) (.imp ψ φ)

end Formula

/-- Turn a frame plus valuation into the ambient model structure. -/
def mkModel {W : Type u} {α : Type v} (F : Frame W) (val : W → α → Prop) : Model W α where
  rel := F.rel
  val := val

notation:50 M ", " w " ⊩ " φ => satisfies M w φ

namespace Frame

variable {W : Type u} {α : Type v}

/-- Validity on a frame ranges over every valuation on that frame. -/
def Valid (F : Frame W) (φ : Formula α) : Prop :=
  ∀ (val : W → α → Prop) (w : W), satisfies (mkModel F val) w φ

end Frame

/-- Accessibility is reflexive. -/
def Reflexive {W : Type u} (F : Frame W) : Prop :=
  ∀ w, F.rel w w

/-- Accessibility is transitive. -/
def Transitive {W : Type u} (F : Frame W) : Prop :=
  ∀ u v w, F.rel u v → F.rel v w → F.rel u w

/-- Accessibility is euclidean. -/
def Euclidean {W : Type u} (F : Frame W) : Prop :=
  ∀ u v w, F.rel u v → F.rel u w → F.rel v w

/-- Accessibility is symmetric. -/
def Symmetric {W : Type u} (F : Frame W) : Prop :=
  ∀ u v, F.rel u v → F.rel v u

/-- Accessibility is exactly equality. -/
def IsIdentityRelation {W : Type u} (F : Frame W) : Prop :=
  ∀ u v, F.rel u v ↔ u = v

end HeytingLean.ModalCategorySets.Propositional
