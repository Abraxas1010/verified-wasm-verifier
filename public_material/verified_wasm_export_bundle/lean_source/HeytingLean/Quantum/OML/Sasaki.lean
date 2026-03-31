import Mathlib.Order.BooleanAlgebra.Defs
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Order.Nucleus
import HeytingLean.Quantum.OML.Core
import HeytingLean.Quantum.Translate.Modality

/-
# Sasaki projection and hook on orthomodular lattices

This file defines the Sasaki projection `a ▷ b := a ⊓ (aᶜ ⊔ b)` and the Sasaki hook
`a ⇒ₛ b := aᶜ ⊔ (a ⊓ b)` on an `OrthomodularLattice`.  We show that these operations enjoy
the basic order-theoretic properties needed in later bridges to the LoF nucleus/Heyting layer:
weak modus ponens, monotonicity in the right argument, the Boolean limit, and a comparison
with nuclei.  All lemmas in the orthomodular section use only the orthomodular axioms—no
distributivity assumptions are introduced.
-/

namespace HeytingLean.Quantum.OML

variable {α : Type _}

-- Boolean algebras carry the canonical orthocomplemented lattice structure.
instance instOrthocomplementedLatticeOfBoolean (α : Type _) [BooleanAlgebra α] :
    OrthocomplementedLattice α where
  compl := compl
  involutive := by intro a; simp
  antitone := by
    intro a b h
    -- Boolean negation is antitone.
    exact (compl_antitone (α := α) h)
  inf_compl := by intro a; simp
  sup_compl := by intro a; simp

/-- Boolean algebras are orthomodular lattices. -/
instance instOrthomodularLatticeOfBoolean (α : Type _) [BooleanAlgebra α] :
    OrthomodularLattice α where
  orthomodular := by
    intro a b h
    -- Boolean orthomodularity collapses to the distributive identity.
    have h_sup : a ⊔ b = b := sup_eq_right.mpr h
    calc
      b = a ⊔ b := by simp [h_sup]
      _ = a ⊔ (compl a ⊓ b) := by
        have hdist := (sup_inf_left (a := a) (b := compl a) (c := b)).symm
        simpa using hdist

section Basic

variable [OrthocomplementedLattice α]

@[simp] lemma compl_le_iff_le_compl {a b : α} :
    OrthocomplementedLattice.compl a ≤ OrthocomplementedLattice.compl b ↔ b ≤ a := by
  constructor <;> intro h
  · simpa [OrthocomplementedLattice.compl_involutive] using
      OrthocomplementedLattice.compl_antitone (α := α) h
  · simpa using
      OrthocomplementedLattice.compl_antitone (α := α) (a := b) (b := a) h

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
      refine (calc
        a = OrthocomplementedLattice.compl (OrthocomplementedLattice.compl a) := by
                simp [OrthocomplementedLattice.compl_involutive]
        _ ≤ OrthocomplementedLattice.compl
              (OrthocomplementedLattice.compl a ⊓ OrthocomplementedLattice.compl b) :=
              h')
    have hb :
        b ≤ OrthocomplementedLattice.compl
          (OrthocomplementedLattice.compl a ⊓ OrthocomplementedLattice.compl b) := by
      have h : OrthocomplementedLattice.compl a ⊓ OrthocomplementedLattice.compl b
          ≤ OrthocomplementedLattice.compl b := inf_le_right
      have h' :=
        OrthocomplementedLattice.compl_antitone (α := α) h
      refine (calc
        b = OrthocomplementedLattice.compl (OrthocomplementedLattice.compl b) := by
                simp [OrthocomplementedLattice.compl_involutive]
        _ ≤ OrthocomplementedLattice.compl
              (OrthocomplementedLattice.compl a ⊓ OrthocomplementedLattice.compl b) :=
              h')
    have hsup :
        a ⊔ b ≤ OrthocomplementedLattice.compl
          (OrthocomplementedLattice.compl a ⊓ OrthocomplementedLattice.compl b) :=
      sup_le ha hb
    have hcompl := OrthocomplementedLattice.compl_antitone (α := α) hsup
    -- rewrite double complement on the right
    have hcompl' :
        OrthocomplementedLattice.compl a ⊓ OrthocomplementedLattice.compl b
          ≤ OrthocomplementedLattice.compl (a ⊔ b) :=
      by
        convert hcompl using 1;
          simp [OrthocomplementedLattice.compl_involutive]
    exact hcompl'

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
    simp [hx']
  · have ha : OrthocomplementedLattice.compl a ≤
        OrthocomplementedLattice.compl (a ⊓ b) :=
      OrthocomplementedLattice.compl_antitone (α := α)
        (inf_le_left : a ⊓ b ≤ a)
    have hb : OrthocomplementedLattice.compl b ≤
        OrthocomplementedLattice.compl (a ⊓ b) :=
      OrthocomplementedLattice.compl_antitone (α := α)
        (inf_le_right : a ⊓ b ≤ b)
    exact sup_le ha hb

/-- Sasaki projection: `a ▷ b := a ⊓ (aᶜ ⊔ b)`, the part of `b` that lies under `a`. -/
@[simp] def sasakiProj (a b : α) : α :=
  a ⊓ (OrthocomplementedLattice.compl a ⊔ b)

/-- Sasaki hook: `a ⇒ₛ b := aᶜ ⊔ (a ⊓ b)`, a quantum conditional enjoying weak modus ponens. -/
@[simp] def sasakiHook (a b : α) : α :=
  OrthocomplementedLattice.compl a ⊔ (a ⊓ b)

infixr:60 " ▷ " => sasakiProj
infixr:50 " ⇒ₛ " => sasakiHook

@[simp] lemma sasakiProj_le_left (a b : α) : sasakiProj a b ≤ a := inf_le_left

/-- Sasaki projection is monotone in its right argument. -/
lemma sasakiProj_monotone_right (a : α) : Monotone fun b => sasakiProj a b := by
  intro b₁ b₂ h
  dsimp [sasakiProj]
  exact inf_le_inf_left _ (sup_le_sup_left h _)

/-- Sasaki hook is monotone in its right argument. -/
lemma sasakiHook_monotone_right (a : α) : Monotone fun b => sasakiHook a b := by
  intro b₁ b₂ h
  dsimp [sasakiHook]
  exact sup_le_sup_left (inf_le_inf_left _ h) _

end Basic

section Orthomodular

variable [OrthocomplementedLattice α] [OrthomodularLattice α]

/-- Orthomodularity expressed via complements, used for Sasaki projection identity. -/
private lemma eq_inf_sup_compl_of_le {a b : α} (h : b ≤ a) :
    b = a ⊓ (b ⊔ OrthocomplementedLattice.compl a) := by
  have hcompl :
      OrthocomplementedLattice.compl a ≤ OrthocomplementedLattice.compl b :=
    OrthocomplementedLattice.compl_antitone (α := α) h
  have horth :
      OrthocomplementedLattice.compl b
        = OrthocomplementedLattice.compl a ⊔
            (a ⊓ OrthocomplementedLattice.compl b) := by
    simpa using
      OrthomodularLattice.orthomodular (α := α)
        (a := OrthocomplementedLattice.compl a)
        (b := OrthocomplementedLattice.compl b) hcompl
  have hcompl' := congrArg OrthocomplementedLattice.compl horth
  simpa [compl_sup, compl_inf, OrthocomplementedLattice.compl_involutive,
    sup_comm, inf_comm, inf_left_comm, inf_assoc] using hcompl'

/-- Sasaki projection acts as the identity on any element beneath the projector. -/
lemma sasakiProj_id_of_le {a b : α} (h : b ≤ a) : sasakiProj a b = b := by
  have := eq_inf_sup_compl_of_le (a := a) (b := b) h
  have h' : a ⊓ (OrthocomplementedLattice.compl a ⊔ b) = b := by
    have h'' := this.symm
    simpa [sup_comm] using h''
  simpa [sasakiProj] using h'

/-- Alias for `sasakiProj_id_of_le` matching traditional presentations. -/
lemma sasakiProj_of_le {a b : α} (h : b ≤ a) : a ▷ b = b :=
  sasakiProj_id_of_le (a := a) (b := b) h

/-- Weak modus ponens for the Sasaki hook: `a ⊓ (a ⇒ₛ b) ≤ b` in any orthomodular lattice. -/
theorem sasaki_mp (a b : α) : a ⊓ sasakiHook a b ≤ b := by
  calc
    a ⊓ sasakiHook a b = sasakiProj a (a ⊓ b) := by rfl
    _ = a ⊓ b :=
      sasakiProj_id_of_le (a := a) (b := a ⊓ b) (inf_le_left : a ⊓ b ≤ a)
    _ ≤ b := inf_le_right

lemma sasaki_weak_mp (a b : α) : a ⊓ sasakiHook a b ≤ b :=
  sasaki_mp (a := a) (b := b)

end Orthomodular

section ClassicalLimit

variable [BooleanAlgebra α]

/-- In a Boolean algebra, the Sasaki hook coincides with material implication. -/
lemma sasakiHook_eq_classical (a b : α) : sasakiHook a b = aᶜ ⊔ b := by
  -- specialize the orthocomplemented instance to the Boolean one
  let _ := instOrthocomplementedLatticeOfBoolean (α := α)
  have h := sup_inf_left (a := aᶜ) (b := a) (c := b)
  calc
    sasakiHook a b = aᶜ ⊔ (a ⊓ b) := rfl
    _ = (aᶜ ⊔ a) ⊓ (aᶜ ⊔ b) := h
    _ = (⊤ : α) ⊓ (aᶜ ⊔ b) := by
      have htop : aᶜ ⊔ a = (⊤ : α) := compl_sup_eq_top (x := a)
      rw [htop]
    _ = aᶜ ⊔ b := by simp [sup_comm]

end ClassicalLimit

section NucleusBridge

variable [OrthocomplementedLattice α]

/-- Base lattice inequality: Sasaki hook sits below the classical implication `aᶜ ⊔ b`. -/
private lemma sasakiHook_le_imp_base (a b : α) :
    sasakiHook a b ≤ OrthocomplementedLattice.compl a ⊔ b := by
  dsimp [sasakiHook]
  refine sup_le ?_ ?_
  · exact le_sup_left
  · exact le_sup_of_le_right inf_le_right

/-- Any nucleus-based implication `n (aᶜ ⊔ b)` dominates the Sasaki hook. -/
lemma sasakiHook_le_nucleus_imp (n : Nucleus α) (a b : α) :
    sasakiHook a b ≤ n (OrthocomplementedLattice.compl a ⊔ b) :=
  (sasakiHook_le_imp_base (a := a) (b := b)).trans
    (Nucleus.le_apply (n := n) (x := OrthocomplementedLattice.compl a ⊔ b))

end NucleusBridge

section ClassicalNucleus

variable [BooleanAlgebra α]

/-- In any Boolean algebra, closing a Sasaki hook with a nucleus coincides with
closing the classical implication `aᶜ ⊔ b`. This is the nucleus-level Boolean
limit needed for working inside fixed-point sublocales (`Omega`). -/
lemma sasakiHook_closure_eq_classical (n : Nucleus α) (a b : α) :
    n (sasakiHook a b) = n (OrthocomplementedLattice.compl a ⊔ b) := by
  have h : sasakiHook a b = OrthocomplementedLattice.compl a ⊔ b := by
    -- On Boolean algebras `aᶜ` is the orthocomplement.
    simpa using (sasakiHook_eq_classical (a := a) (b := b))
  calc
    n (sasakiHook a b) = n (OrthocomplementedLattice.compl a ⊔ b) := by
      rw [h]

end ClassicalNucleus

end HeytingLean.Quantum.OML
