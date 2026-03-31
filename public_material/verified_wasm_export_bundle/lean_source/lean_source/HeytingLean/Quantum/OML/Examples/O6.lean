import HeytingLean.Quantum.OML.Core

open scoped Classical

namespace HeytingLean.Quantum.OML

inductive O6
| bot | u | u' | v | v' | top
deriving DecidableEq, Repr

namespace O6
open O6

def compl : O6 → O6
| bot => top
| top => bot
| u   => u'
| u'  => u
| v   => v'
| v'  => v

def inf : O6 → O6 → O6
| bot, _ => bot
| _, bot => bot
| top, x => x
| x, top => x
| u, u => u
| u', u' => u'
| v, v => v
| v', v' => v'
| _, _ => bot

def sup : O6 → O6 → O6
| top, _ => top
| _, top => top
| bot, x => x
| x, bot => x
| u, u => u
| u', u' => u'
| v, v => v
| v', v' => v'
| _, _ => top

def le : O6 → O6 → Prop
| bot, _ => True
| _, top => True
| u, u => True
| u', u' => True
| v, v => True
| v', v' => True
| _, _ => False

instance : LE O6 where
  le := le

lemma le_def {x y : O6} : (x ≤ y) =
  match x, y with
  | bot, _ => True
  | _, top => True
  | u, u => True
  | u', u' => True
  | v, v => True
  | v', v' => True
  | _, _ => False := rfl

@[simp] lemma le_bot {x} : (x ≤ bot) = (x = bot) := by
  cases x <;> simp [le_def]

@[simp] lemma top_le {x} : (top ≤ x) = (x = top) := by
  cases x <;> simp [le_def]

lemma le_refl' (x : O6) : x ≤ x := by
  cases x <;> simp [le_def]

lemma le_trans' (x y z : O6) : x ≤ y → y ≤ z → x ≤ z := by
  cases x <;> cases y <;> cases z <;> simp [le_def]

lemma le_antisymm' (x y : O6) : x ≤ y → y ≤ x → x = y := by
  cases x <;> cases y <;> simp [le_def]

instance : LE O6 where
  le := le

instance : Preorder O6 where
  le := (· ≤ ·)
  le_refl := le_refl'
  le_trans := le_trans'

instance : PartialOrder O6 where
  le := (· ≤ ·)
  le_refl := le_refl'
  le_trans := le_trans'
  le_antisymm := le_antisymm'

instance : OrderBot O6 where
  bot := bot
  bot_le := by
    intro x; cases x <;> simp [le_def]

instance : OrderTop O6 where
  top := top
  le_top := by
    intro x; cases x <;> simp [le_def]

instance : BoundedOrder O6 where
  __ := (inferInstance : OrderTop O6)
  __ := (inferInstance : OrderBot O6)

lemma inf_le_left' (x y : O6) : inf x y ≤ x := by
  cases x <;> cases y <;> simp [inf, le_def]

lemma inf_le_right' (x y : O6) : inf x y ≤ y := by
  cases x <;> cases y <;> simp [inf, le_def]

lemma le_sup_left' (x y : O6) : x ≤ sup x y := by
  cases x <;> cases y <;> simp [sup, le_def]

lemma le_sup_right' (x y : O6) : y ≤ sup x y := by
  cases x <;> cases y <;> simp [sup, le_def]

lemma le_inf' (x y z : O6) : x ≤ y → x ≤ z → x ≤ inf y z := by
  cases x <;> cases y <;> cases z <;> intro h1 h2 <;> simp [inf, le_def] at h1 h2 ⊢

lemma sup_le' (x y z : O6) : x ≤ z → y ≤ z → sup x y ≤ z := by
  cases x <;> cases y <;> cases z <;> intro h1 h2 <;> simp [sup, le_def] at h1 h2 ⊢

instance : SemilatticeInf O6 where
  le := (· ≤ ·)
  le_refl := le_refl'
  le_trans := le_trans'
  le_antisymm := le_antisymm'
  inf := inf
  inf_le_left := inf_le_left'
  inf_le_right := inf_le_right'
  le_inf := fun x y z => le_inf' x y z

instance : SemilatticeSup O6 where
  le := (· ≤ ·)
  le_refl := le_refl'
  le_trans := le_trans'
  le_antisymm := le_antisymm'
  sup := sup
  le_sup_left := le_sup_left'
  le_sup_right := le_sup_right'
  sup_le := fun x y z => sup_le' x y z

instance : Lattice O6 where
  __ := (inferInstance : SemilatticeSup O6)
  __ := (inferInstance : SemilatticeInf O6)

instance : OrthocomplementedLattice O6 where
  compl := compl
  involutive := by intro a; cases a <;> rfl
  antitone := by intro a b h; cases a <;> cases b <;> simp [le_def, compl] at *
  inf_compl := by intro a; cases a <;> rfl
  sup_compl := by intro a; cases a <;> rfl

instance : OrthomodularLattice O6 where
  orthomodular := by
    intro a b hab
    cases a <;> cases b <;> cases hab <;> decide

lemma nondistrib :
  inf u (sup v v') ≠ sup (inf u v) (inf u v') := by
  simp [inf, sup]

end O6

end HeytingLean.Quantum.OML
