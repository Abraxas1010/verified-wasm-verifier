import Mathlib.CategoryTheory.Category.Basic

/-!
# IteratedVirtual.GlobularIndex

An explicit **globular indexing category** `𝔾` (“globe category”), in a minimal strict form:

- Objects are natural numbers (dimensions).
- There are no morphisms `m ⟶ n` when `n < m`.
- For `m = n`, there is exactly the identity morphism.
- For `m < n`, there are exactly two morphisms, corresponding to “source” / “target” at the
  *domain* dimension.

Composition is left-biased: when both arrows are non-identities, the composite keeps the left
arrow’s source/target choice. This encodes the standard globular relations
`s_n ≫ s_{n+1} = s_n ≫ t_{n+1}` and `t_n ≫ s_{n+1} = t_n ≫ t_{n+1}`.
-/

namespace HeytingLean
namespace IteratedVirtual

namespace GlobularIndex

/-- Wrapper type for the globular indexing category objects. -/
structure Obj where
  n : Nat
deriving DecidableEq, Repr

abbrev ofNat (n : Nat) : Obj := ⟨n⟩

/-- Morphisms in the globular indexing category. -/
structure Hom (a b : Obj) where
  /-- `none` is identity (when `a = b`); `some false/true` is the source/target choice (when `a < b`). -/
  kind : Option Bool
  valid : match kind with
    | none => a = b
    | some _ => a.n < b.n

namespace Hom

@[ext] theorem ext {a b : Obj} {f g : Hom a b} (h : f.kind = g.kind) : f = g := by
  cases f with
  | mk fk fv =>
    cases g with
    | mk gk gv =>
      cases h
      have : fv = gv := Subsingleton.elim _ _
      cases this
      rfl

def id (a : Obj) : Hom a a :=
  { kind := none
    valid := rfl }

def src (n : Nat) : Hom (ofNat n) (ofNat (n + 1)) :=
  { kind := some false
    valid := Nat.lt_succ_self n }

def tgt (n : Nat) : Hom (ofNat n) (ofNat (n + 1)) :=
  { kind := some true
    valid := Nat.lt_succ_self n }

def comp {a b c : Obj} (f : Hom a b) (g : Hom b c) : Hom a c :=
  match f with
  | ⟨none, hab⟩ => by
      cases hab
      exact g
  | ⟨some fb, hab⟩ =>
      match g with
      | ⟨none, hbc⟩ => by
          cases hbc
          exact ⟨some fb, hab⟩
      | ⟨some _, hbc⟩ =>
          ⟨some fb, Nat.lt_trans hab hbc⟩

@[simp] theorem comp_kind_some {a b c : Obj} (fb : Bool) (fvalid : a.n < b.n) (g : Hom b c) :
    (comp (a := a) (b := b) (c := c) { kind := some fb, valid := fvalid } g).kind = some fb := by
  cases g with
  | mk gkind gvalid =>
    cases gkind with
    | none =>
        cases gvalid
        simp [comp]
    | some _ =>
        simp [comp]

end Hom

instance : CategoryTheory.Category Obj where
  Hom a b := Hom a b
  id a := Hom.id a
  comp f g := Hom.comp f g
  id_comp := by
    intro a b f
    cases f with
    | mk kind valid =>
      cases kind with
      | none =>
        cases valid
        -- now `f` is an identity, and proof fields are Prop (proof-irrelevant)
        apply Hom.ext
        rfl
      | some _ =>
        apply Hom.ext
        rfl
  comp_id := by
    intro a b f
    cases f with
    | mk kind valid =>
      cases kind with
      | none =>
        cases valid
        apply Hom.ext
        rfl
      | some _ =>
        apply Hom.ext
        rfl
  assoc := by
    intro a b c d f g h
    cases f with
    | mk fkind fvalid =>
      cases fkind with
      | none =>
        cases fvalid
        apply Hom.ext
        rfl
      | some fb =>
        cases g with
        | mk gkind gvalid =>
          cases h with
          | mk hkind hvalid =>
            -- Both sides of associativity are left-biased to `fb`.
            apply Hom.ext
            cases gkind with
            | none =>
                cases gvalid
                cases hkind with
                | none =>
                    cases hvalid
                    simp [Hom.comp]
                | some _ =>
                    simp [Hom.comp]
            | some _ =>
                cases hkind with
                | none =>
                    cases hvalid
                    simp [Hom.comp]
                | some _ =>
                    simp [Hom.comp]

/-- The generating source morphism `s_n : n ⟶ n+1`. -/
abbrev src (n : Nat) : ofNat n ⟶ ofNat (n + 1) := Hom.src n

/-- The generating target morphism `t_n : n ⟶ n+1`. -/
abbrev tgt (n : Nat) : ofNat n ⟶ ofNat (n + 1) := Hom.tgt n

/-- Globular relation `s_n ≫ s_{n+1} = s_n ≫ t_{n+1}` as an equality in `GlobularIndex`. -/
theorem src_src_eq_src_tgt (n : Nat) :
    Hom.comp (Hom.src n) (Hom.src (n + 1)) = Hom.comp (Hom.src n) (Hom.tgt (n + 1)) := by
  rfl

/-- Globular relation `t_n ≫ s_{n+1} = t_n ≫ t_{n+1}` as an equality in `GlobularIndex`. -/
theorem tgt_src_eq_tgt_tgt (n : Nat) :
    Hom.comp (Hom.tgt n) (Hom.src (n + 1)) = Hom.comp (Hom.tgt n) (Hom.tgt (n + 1)) := by
  rfl

end GlobularIndex

end IteratedVirtual
end HeytingLean
