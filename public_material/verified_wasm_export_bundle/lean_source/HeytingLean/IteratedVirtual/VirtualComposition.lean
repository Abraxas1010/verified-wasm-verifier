import HeytingLean.IteratedVirtual.Cobordism

/-!
# IteratedVirtual.VirtualComposition

Formal (“virtual”) composition of cobordisms: we represent a composite as a chain of
cobordisms, without attempting to compute/paste them in a specific virtual double category.
-/

namespace HeytingLean
namespace IteratedVirtual

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]

/-- A formal composite of cobordisms from `A` to `B`. -/
inductive CobordismChain {X Y : C} {n : Nat} :
    IteratedCellOver (C := C) X Y n → IteratedCellOver (C := C) X Y n → Type (max u v)
  | nil (A : IteratedCellOver (C := C) X Y n) : CobordismChain A A
  | cons {A B D : IteratedCellOver (C := C) X Y n} :
      CobordismOver (C := C) A B → CobordismChain B D → CobordismChain A D

namespace CobordismChain

def length {X Y : C} {n : Nat} {A B : IteratedCellOver (C := C) X Y n} :
    CobordismChain (C := C) A B → Nat
  | nil _ => 0
  | cons _ rest => rest.length.succ

def append {X Y : C} {n : Nat} {A B D : IteratedCellOver (C := C) X Y n} :
    CobordismChain (C := C) A B → CobordismChain (C := C) B D → CobordismChain (C := C) A D
  | nil _, q => q
  | cons h p, q => cons h (append p q)

@[simp] theorem append_nil_left {X Y : C} {n : Nat} {A B : IteratedCellOver (C := C) X Y n}
    (p : CobordismChain (C := C) A B) :
    append (CobordismChain.nil A) p = p := by
  rfl

@[simp] theorem append_nil_right {X Y : C} {n : Nat} {A B : IteratedCellOver (C := C) X Y n}
    (p : CobordismChain (C := C) A B) :
    append p (CobordismChain.nil B) = p := by
  induction p with
  | nil A =>
      rfl
  | cons h rest ih =>
      simp [append, ih]

@[simp] theorem append_assoc {X Y : C} {n : Nat}
    {A B D E : IteratedCellOver (C := C) X Y n}
    (p : CobordismChain (C := C) A B)
    (q : CobordismChain (C := C) B D)
    (r : CobordismChain (C := C) D E) :
    append (append p q) r = append p (append q r) := by
  induction p with
  | nil A =>
      rfl
  | cons h rest ih =>
      simp [append, ih]

end CobordismChain

/-!
## Virtual cobordisms between parallel morphisms

For `f,g : X ⟶ Y`, view them as `n = 1` cells via `IteratedCellOver.ofHom`, and take a
`CobordismChain` between them.
-/

abbrev VirtualCobordismHom {X Y : C} (f g : X ⟶ Y) : Type (max u v) :=
  CobordismChain (C := C) (n := 1) (IteratedCellOver.ofHom (C := C) f) (IteratedCellOver.ofHom (C := C) g)

namespace VirtualCobordismHom

def refl {X Y : C} (f : X ⟶ Y) : VirtualCobordismHom (C := C) f f :=
  CobordismChain.nil (C := C) (n := 1) (IteratedCellOver.ofHom (C := C) f)

end VirtualCobordismHom

/-!
## Coherence as strict category laws

With morphisms as cobordism chains and composition as `append`, the coherence laws become
definitional/inductive equalities (associativity and identities).
-/

instance cobordismChainCategory {X Y : C} (n : Nat) : Category (IteratedCellOver (C := C) X Y n) where
  Hom A B := CobordismChain (C := C) (n := n) A B
  id A := CobordismChain.nil (C := C) (n := n) A
  comp p q := CobordismChain.append (C := C) (n := n) p q
  id_comp := by intro A B p; simp
  comp_id := by intro A B p; simp
  assoc := by
    intro A B D E p q r
    simp [CobordismChain.append_assoc]

end IteratedVirtual
end HeytingLean
