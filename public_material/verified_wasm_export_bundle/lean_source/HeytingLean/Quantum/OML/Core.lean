import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic

/-!
Defines orthocomplemented and orthomodular lattices as standalone classes so
that other quantum modules can reason abstractly about orthocomplementation.
-/

open scoped Classical

namespace HeytingLean.Quantum.OML

class OrthocomplementedLattice (α : Type _)
  extends Lattice α, BoundedOrder α where
  compl : α → α
  involutive : ∀ a, compl (compl a) = a
  antitone : ∀ {a b}, a ≤ b → compl b ≤ compl a
  inf_compl : ∀ a, a ⊓ compl a = ⊥
  sup_compl : ∀ a, a ⊔ compl a = ⊤

namespace OrthocomplementedLattice

variable {α : Type _} [OrthocomplementedLattice α]

@[simp] instance instHasCompl : HasCompl α := ⟨OrthocomplementedLattice.compl⟩

@[simp] lemma compl_involutive (a : α) :
    OrthocomplementedLattice.compl
      (OrthocomplementedLattice.compl a) = a :=
  OrthocomplementedLattice.involutive (α := α) a

lemma compl_antitone {a b : α} (h : a ≤ b) :
    OrthocomplementedLattice.compl b ≤ OrthocomplementedLattice.compl a :=
  OrthocomplementedLattice.antitone (α := α) (a := a) (b := b) h

@[simp] lemma compl_le_iff_le_compl {a b : α} :
    OrthocomplementedLattice.compl a ≤ OrthocomplementedLattice.compl b ↔ b ≤ a := by
  constructor <;> intro h
  · simpa [OrthocomplementedLattice.compl_involutive] using
      OrthocomplementedLattice.compl_antitone (α := α) h
  · simpa using OrthocomplementedLattice.compl_antitone (α := α) (a := b) (b := a) h

@[simp] lemma inf_compl_eq_bot (a : α) :
    a ⊓ OrthocomplementedLattice.compl a = ⊥ :=
  OrthocomplementedLattice.inf_compl (α := α) a

@[simp] lemma sup_compl_eq_top (a : α) :
    a ⊔ OrthocomplementedLattice.compl a = ⊤ :=
  OrthocomplementedLattice.sup_compl (α := α) a

@[simp] lemma compl_sup (a b : α) :
    OrthocomplementedLattice.compl (a ⊔ b)
      = OrthocomplementedLattice.compl a ⊓ OrthocomplementedLattice.compl b := by
  apply le_antisymm
  · refine le_inf ?_ ?_
    · exact OrthocomplementedLattice.compl_antitone (α := α) (le_sup_left : a ≤ a ⊔ b)
    · exact OrthocomplementedLattice.compl_antitone (α := α) (le_sup_right : b ≤ a ⊔ b)
  · have ha :
        a ≤ OrthocomplementedLattice.compl
          (OrthocomplementedLattice.compl a ⊓ OrthocomplementedLattice.compl b) := by
      have h : OrthocomplementedLattice.compl a ⊓ OrthocomplementedLattice.compl b
          ≤ OrthocomplementedLattice.compl a := inf_le_left
      have h' :=
        OrthocomplementedLattice.compl_antitone (α := α) h
      -- rewrite away the double complement on `a`
      simpa [OrthocomplementedLattice.compl_involutive] using h'
    have hb :
        b ≤ OrthocomplementedLattice.compl
          (OrthocomplementedLattice.compl a ⊓ OrthocomplementedLattice.compl b) := by
      have h : OrthocomplementedLattice.compl a ⊓ OrthocomplementedLattice.compl b
          ≤ OrthocomplementedLattice.compl b := inf_le_right
      have h' :=
        OrthocomplementedLattice.compl_antitone (α := α) h
      simpa [OrthocomplementedLattice.compl_involutive] using h'
    have hsup :
        a ⊔ b ≤ OrthocomplementedLattice.compl
          (OrthocomplementedLattice.compl a ⊓ OrthocomplementedLattice.compl b) :=
      sup_le ha hb
    have hcompl := OrthocomplementedLattice.compl_antitone (α := α) hsup
    -- rewrite double complement on the right
    simpa [OrthocomplementedLattice.compl_involutive] using hcompl

@[simp] lemma compl_inf (a b : α) :
    OrthocomplementedLattice.compl (a ⊓ b)
      = OrthocomplementedLattice.compl a ⊔ OrthocomplementedLattice.compl b := by
  apply le_antisymm
  · apply
      (OrthocomplementedLattice.compl_le_iff_le_compl (α := α)).1
    have hx' :
        OrthocomplementedLattice.compl
          (OrthocomplementedLattice.compl a ⊔ OrthocomplementedLattice.compl b)
        = a ⊓ b := by
      calc
        OrthocomplementedLattice.compl
            (OrthocomplementedLattice.compl a ⊔ OrthocomplementedLattice.compl b)
            =
            OrthocomplementedLattice.compl (OrthocomplementedLattice.compl a)
              ⊓ OrthocomplementedLattice.compl (OrthocomplementedLattice.compl b) :=
          OrthocomplementedLattice.compl_sup (α := α)
            (a := OrthocomplementedLattice.compl a)
            (b := OrthocomplementedLattice.compl b)
        _ = a ⊓ b := by
          simp [OrthocomplementedLattice.compl_involutive]
    -- rewrite `hx` into the goal
    simp [hx', OrthocomplementedLattice.compl_involutive]
  · have ha : OrthocomplementedLattice.compl a ≤
        OrthocomplementedLattice.compl (a ⊓ b) :=
      OrthocomplementedLattice.compl_antitone (α := α)
        (inf_le_left : a ⊓ b ≤ a)
    have hb : OrthocomplementedLattice.compl b ≤
        OrthocomplementedLattice.compl (a ⊓ b) :=
      OrthocomplementedLattice.compl_antitone (α := α)
        (inf_le_right : a ⊓ b ≤ b)
    exact sup_le ha hb

end OrthocomplementedLattice

class OrthomodularLattice (α : Type _) [OrthocomplementedLattice α] : Prop where
  orthomodular :
    ∀ {a b : α}, a ≤ b →
      b = a ⊔ (OrthocomplementedLattice.compl a ⊓ b)

namespace OrthomodularLattice

variable {α : Type _} [OrthocomplementedLattice α] [OrthomodularLattice α]

lemma eq_inf_sup_compl_of_le {a b : α} (h : a ≤ b) :
    a = b ⊓ (a ⊔ OrthocomplementedLattice.compl b) := by
  have hcompl :
      OrthocomplementedLattice.compl b ≤ OrthocomplementedLattice.compl a :=
    OrthocomplementedLattice.compl_antitone (α := α) h
  have horth :
      OrthocomplementedLattice.compl a
        = OrthocomplementedLattice.compl b ⊔
            (b ⊓ OrthocomplementedLattice.compl a) := by
    simpa using
      OrthomodularLattice.orthomodular (α := α)
        (a := OrthocomplementedLattice.compl b)
        (b := OrthocomplementedLattice.compl a) hcompl
  have hcompl' := congrArg OrthocomplementedLattice.compl horth
  simpa [OrthocomplementedLattice.compl_sup, OrthocomplementedLattice.compl_inf,
    OrthocomplementedLattice.compl_involutive, sup_comm, inf_comm, inf_left_comm, inf_assoc]
    using hcompl'

lemma proj_id_of_le {a x : α} (h : x ≤ a) :
    a ⊓ (OrthocomplementedLattice.compl a ⊔ x) = x := by
  have := eq_inf_sup_compl_of_le (a := x) (b := a) h
  simpa [sup_comm] using this.symm

end OrthomodularLattice

end HeytingLean.Quantum.OML
