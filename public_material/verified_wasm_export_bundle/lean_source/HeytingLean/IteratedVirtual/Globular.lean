import Mathlib.CategoryTheory.Category.Basic

/-!
# IteratedVirtual.Globular

Minimal globular-set primitives (sufficient to define walking `k`-globes and “k-cells as maps
from globes”).

We intentionally keep this *small and local*; Mathlib does not currently ship a globular-set API
at this repo pin (see `WIP/monad_noah_research_map_2026-01-29.md`).
-/

namespace HeytingLean
namespace IteratedVirtual

universe u v

/-- A globular set presented as levels `Cell n` with source/target maps satisfying the
globular identities. -/
structure GlobularSet where
  Cell : Nat → Type u
  src : {n : Nat} → Cell (n + 1) → Cell n
  tgt : {n : Nat} → Cell (n + 1) → Cell n
  src_src_eq_src_tgt : ∀ {n : Nat} (x : Cell (n + 2)), src (src x) = src (tgt x)
  tgt_src_eq_tgt_tgt : ∀ {n : Nat} (x : Cell (n + 2)), tgt (src x) = tgt (tgt x)

namespace GlobularSet

/-- Morphisms of globular sets. -/
structure Hom (X Y : GlobularSet.{u}) where
  map : ∀ n : Nat, X.Cell n → Y.Cell n
  map_src : ∀ n : Nat, ∀ x : X.Cell (n + 1), map n (X.src x) = Y.src (map (n + 1) x)
  map_tgt : ∀ n : Nat, ∀ x : X.Cell (n + 1), map n (X.tgt x) = Y.tgt (map (n + 1) x)

attribute [simp] Hom.map_src Hom.map_tgt

@[ext] theorem Hom.ext {X Y : GlobularSet.{u}} {f g : Hom X Y}
    (h : ∀ n : Nat, ∀ x : X.Cell n, f.map n x = g.map n x) : f = g := by
  cases f with
  | mk fmap fsrc ftgt =>
    cases g with
    | mk gmap gsrc gtgt =>
      have hm : fmap = gmap := by
        funext n x
        exact h n x
      subst hm
      have hsrc : fsrc = gsrc := by
        funext n x
        exact Subsingleton.elim (fsrc n x) (gsrc n x)
      have htgt : ftgt = gtgt := by
        funext n x
        exact Subsingleton.elim (ftgt n x) (gtgt n x)
      subst hsrc
      subst htgt
      rfl

/-- Identity morphism. -/
def Hom.id (X : GlobularSet.{u}) : Hom X X :=
  { map := fun _ x => x
    map_src := by intro n x; rfl
    map_tgt := by intro n x; rfl }

/-- Composition of globular-set morphisms. -/
def Hom.comp {X Y Z : GlobularSet.{u}} (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  { map := fun n => g.map n ∘ f.map n
    map_src := by
      intro n x
      simp [Function.comp, f.map_src, g.map_src]
    map_tgt := by
      intro n x
      simp [Function.comp, f.map_tgt, g.map_tgt] }

instance : CategoryTheory.Category GlobularSet.{u} where
  Hom X Y := Hom X Y
  id X := Hom.id X
  comp f g := Hom.comp f g
  id_comp := by
    intro X Y f
    ext n x
    rfl
  comp_id := by
    intro X Y f
    ext n x
    rfl
  assoc := by
    intro W X Y Z f g h
    ext n x
    rfl

end GlobularSet

end IteratedVirtual
end HeytingLean
