import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.PNat.Defs

import HeytingLean.Layouts.Tuple.Fin0

/-!
# The flat `Tuple` category (CuTe layouts)

Objects are tuples of positive integers (dimension sizes).

Morphisms are *pointed* maps between the corresponding pointed finite sets of dimension indices,
with:
- basepoint preservation,
- injectivity away from the basepoint, and
- dimension-label preservation.

This is the flat `Tuple` category from the CuTe layout-categories development.
-/

namespace HeytingLean
namespace Layouts
namespace Tuple

/-- Objects: tuples of positive integers. -/
abbrev Obj : Type := List ℕ+

namespace Obj

/-- Number of dimensions. -/
def rank (S : Obj) : ℕ := S.length

/-- Size (product of dimensions). -/
def size (S : Obj) : ℕ :=
  S.foldl (fun acc s => acc * s.val) 1

instance : Inhabited Obj := ⟨[]⟩

end Obj

/-- Morphisms in `Tuple`. -/
structure Mor (S T : Obj) where
  hom : Fin0Hom S.length T.length

  /-- Dimension preservation: `i ↦ j` (non-basepoint) preserves the dimension label. -/
  dim_pres :
    ∀ (i : Fin S.length) (j : Fin T.length),
      hom (some i) = some j → S.get i = T.get j

  /-- Injective away from basepoint: if two indices map to the same `j`, they are equal. -/
  inj_away :
    ∀ (i i' : Fin S.length) (j : Fin T.length),
      hom (some i) = some j → hom (some i') = some j → i = i'

namespace Mor

instance {S T : Obj} : CoeFun (Mor S T) (fun _ => Fin0 S.length → Fin0 T.length) :=
  ⟨fun f => f.hom⟩

@[ext] theorem ext {S T : Obj} {f g : Mor S T} (h : f.hom.toFun = g.hom.toFun) : f = g := by
  cases f with
  | mk fHom fDim fInj =>
    cases g with
    | mk gHom gDim gInj =>
      have hHom : fHom = gHom := by
        apply Fin0Hom.ext
        exact h
      cases hHom
      have hDim : fDim = gDim := by apply Subsingleton.elim
      have hInj : fInj = gInj := by apply Subsingleton.elim
      cases hDim
      cases hInj
      rfl

def id (S : Obj) : Mor S S where
  hom := Fin0Hom.id S.length
  dim_pres := by
    intro i j hij
    cases hij
    rfl
  inj_away := by
    intro i i' j hi hi'
    cases hi
    cases hi'
    rfl

def comp {S T U : Obj} (g : Mor T U) (f : Mor S T) : Mor S U where
  hom := Fin0Hom.comp g.hom f.hom
  dim_pres := by
    intro i k hik
    -- `g (f i) = k` forces `f i` to be non-basepoint.
    cases hfj : f.hom (some i) with
    | none =>
        have hgn : g.hom none = some k := by
          simpa [Fin0Hom.comp_apply, hfj] using hik
        -- but `g` preserves the basepoint
        simp [g.hom.map_base] at hgn
    | some j =>
        have hg : g.hom (some j) = some k := by
          simpa [Fin0Hom.comp_apply, hfj] using hik
        have hs : S.get i = T.get j := f.dim_pres i j hfj
        have ht : T.get j = U.get k := g.dim_pres j k hg
        exact hs.trans ht
  inj_away := by
    intro i i' k hi hi'
    cases hfi : f.hom (some i) with
    | none =>
        have hgn : g.hom none = some k := by
          simpa [Fin0Hom.comp_apply, hfi] using hi
        simp [g.hom.map_base] at hgn
    | some j =>
        cases hfi' : f.hom (some i') with
        | none =>
            have hgn : g.hom none = some k := by
              simpa [Fin0Hom.comp_apply, hfi'] using hi'
            simp [g.hom.map_base] at hgn
        | some j' =>
            have hg : g.hom (some j) = some k := by
              simpa [Fin0Hom.comp_apply, hfi] using hi
            have hg' : g.hom (some j') = some k := by
              simpa [Fin0Hom.comp_apply, hfi'] using hi'
            have hj : j = j' := g.inj_away j j' k hg hg'
            cases hj
            exact f.inj_away i i' j hfi hfi'

end Mor

open CategoryTheory

instance : Category Obj where
  Hom S T := Mor S T
  id S := Mor.id S
  comp f g := Mor.comp g f
  id_comp := by
    intro S T f
    apply Mor.ext
    rfl
  comp_id := by
    intro S T f
    apply Mor.ext
    rfl
  assoc := by
    intro S T U V f g h
    apply Mor.ext
    rfl

end Tuple
end Layouts
end HeytingLean
