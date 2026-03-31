import HeytingLean.Quantum.OML.Core

open scoped Classical

namespace HeytingLean.Quantum.OML

/-- Finite Hilbert 2D subspace lattice (Boolean): {⊥, X, Y, ⊤} with Xᶜ=Y, Yᶜ=X. -/
inductive H2
| bot | X | Y | top
deriving DecidableEq, Repr

namespace H2
open H2

def compl : H2 → H2
| bot => top
| top => bot
| X => Y
| Y => X

def inf : H2 → H2 → H2
| bot, _ => bot
| _, bot => bot
| top, a => a
| a, top => a
| X, X => X
| Y, Y => Y
| _, _ => bot

def sup : H2 → H2 → H2
| top, _ => top
| _, top => top
| bot, a => a
| a, bot => a
| X, X => X
| Y, Y => Y
| _, _ => top

def le : H2 → H2 → Prop
| bot, _ => True
| _, top => True
| X, X => True
| Y, Y => True
| _, _ => False

instance : LE H2 where
  le := le

@[simp] lemma le_def {a b : H2} : (a ≤ b) =
  match a, b with
  | bot, _ => True
  | _, top => True
  | X, X => True
  | Y, Y => True
  | _, _ => False := rfl

lemma le_refl (a : H2) : a ≤ a := by cases a <;> simp [le_def]

lemma le_trans' (a b c : H2) : a ≤ b → b ≤ c → a ≤ c := by
  cases a <;> cases b <;> cases c <;> simp [le_def]

lemma le_antisymm' (a b : H2) : a ≤ b → b ≤ a → a = b := by
  cases a <;> cases b <;> simp [le_def]

instance : Preorder H2 where
  le := (· ≤ ·)
  le_refl := le_refl
  le_trans := le_trans'

instance : PartialOrder H2 where
  le := (· ≤ ·)
  le_refl := le_refl
  le_trans := le_trans'
  le_antisymm := le_antisymm'

instance : OrderBot H2 where
  bot := bot
  bot_le := by intro a; cases a <;> simp [le_def]

instance : OrderTop H2 where
  top := top
  le_top := by intro a; cases a <;> simp [le_def]

instance : BoundedOrder H2 where
  __ := (inferInstance : OrderTop H2)
  __ := (inferInstance : OrderBot H2)

lemma le_inf_iff {a b c : H2} : a ≤ inf b c ↔ a ≤ b ∧ a ≤ c := by
  cases a <;> cases b <;> cases c <;> simp [inf, le_def]
lemma sup_le_iff {a b c : H2} : sup a b ≤ c ↔ a ≤ c ∧ b ≤ c := by
  cases a <;> cases b <;> cases c <;> simp [sup, le_def]
lemma inf_le_left (a b : H2) : inf a b ≤ a := by cases a <;> cases b <;> simp [inf, le_def]
lemma inf_le_right (a b : H2) : inf a b ≤ b := by cases a <;> cases b <;> simp [inf, le_def]
lemma le_sup_left (a b : H2) : a ≤ sup a b := by cases a <;> cases b <;> simp [sup, le_def]
lemma le_sup_right (a b : H2) : b ≤ sup a b := by cases a <;> cases b <;> simp [sup, le_def]

lemma le_inf {a b c : H2} : a ≤ b → a ≤ c → a ≤ inf b c := by
  intro h1 h2
  cases a <;> cases b <;> cases c <;> simp [inf, le_def] at h1 h2 ⊢

lemma sup_le {a b c : H2} : a ≤ c → b ≤ c → sup a b ≤ c := by
  intro h1 h2
  cases a <;> cases b <;> cases c <;> simp [sup, le_def] at h1 h2 ⊢

instance : SemilatticeInf H2 where
  le := (· ≤ ·)
  le_refl := le_refl
  le_trans := le_trans'
  le_antisymm := le_antisymm'
  inf := inf
  inf_le_left := inf_le_left
  inf_le_right := inf_le_right
  le_inf := fun _ _ _ => le_inf

instance : SemilatticeSup H2 where
  le := (· ≤ ·)
  le_refl := le_refl
  le_trans := le_trans'
  le_antisymm := le_antisymm'
  sup := sup
  le_sup_left := le_sup_left
  le_sup_right := le_sup_right
  sup_le := fun _ _ _ => sup_le

instance : Lattice H2 where
  __ := (inferInstance : SemilatticeSup H2)
  __ := (inferInstance : SemilatticeInf H2)

instance : OrthocomplementedLattice H2 where
  compl := compl
  involutive := by intro a; cases a <;> rfl
  antitone := by intro a b h; cases a <;> cases b <;> simp [le_def, compl] at *
  inf_compl := by intro a; cases a <;> rfl
  sup_compl := by intro a; cases a <;> rfl

instance : OrthomodularLattice H2 where
  orthomodular := by
    intro a b hab
    cases a <;> cases b <;> cases hab <;> decide

end H2

end HeytingLean.Quantum.OML
