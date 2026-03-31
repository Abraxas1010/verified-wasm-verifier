import Mathlib.Data.Fin.Basic
import HeytingLean.ModalCategorySets.Propositional.Core

namespace HeytingLean.ModalCategorySets.Propositional

universe u

/-- The equality frame on any type of worlds. -/
def reflFrame (W : Type u) : Frame W where
  rel x y := x = y

theorem reflFrame_isIdentityRelation (W : Type u) :
    IsIdentityRelation (reflFrame W) := by
  intro x y
  rfl

/-- Finite linear-order frame on `Fin n` using `≤` as accessibility. -/
def linearOrderFrame (n : ℕ) : Frame (Fin n) where
  rel i j := i.1 ≤ j.1

theorem linearOrderFrame_reflexive (n : ℕ) :
    Reflexive (linearOrderFrame n) := by
  intro i
  exact le_rfl

theorem linearOrderFrame_transitive (n : ℕ) :
    Transitive (linearOrderFrame n) := by
  intro i j k hij hjk
  exact Nat.le_trans hij hjk

/-- Any two successors of the same world have a common successor. -/
def DirectedFrame {W : Type u} (F : Frame W) : Prop :=
  ∀ w u v, F.rel w u → F.rel w v → ∃ z, F.rel u z ∧ F.rel v z

end HeytingLean.ModalCategorySets.Propositional
