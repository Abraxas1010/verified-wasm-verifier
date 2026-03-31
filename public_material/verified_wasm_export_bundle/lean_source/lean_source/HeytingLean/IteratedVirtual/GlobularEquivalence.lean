import Mathlib.CategoryTheory.Equivalence
import HeytingLean.IteratedVirtual.GlobularFromPresheaf
import HeytingLean.IteratedVirtual.GlobularToPresheaf
import HeytingLean.IteratedVirtual.GlobularRoundTrip
import HeytingLean.IteratedVirtual.GlobularRoundTripPsh

/-!
# IteratedVirtual.GlobularEquivalence

Phase‑8 strict-only hygiene: package the bridge between the legacy minimal `GlobularSet` record and
the presheaf presentation `GlobularSetPsh := GlobularIndexᵒᵖ ⥤ Type` as an **equivalence of
categories**.

The key data are:
- `GlobularSet.toPresheaf : GlobularSet → GlobularSetPsh` (structured → presheaf),
- `GlobularSetPsh.toGlobularSet : GlobularSetPsh → GlobularSet` (presheaf → structured),
and the round-trip isomorphisms already proved in:
- `GlobularRoundTrip.lean` (structured→presheaf→structured),
- `GlobularRoundTripPsh.lean` (presheaf→structured→presheaf).
-/

namespace HeytingLean
namespace IteratedVirtual

open CategoryTheory

universe u

namespace GlobularSet

/-- A globular-set morphism commutes with `downSrc`. -/
theorem Hom.map_downSrc {X Y : GlobularSet.{u}} (f : X ⟶ Y) :
    ∀ (m n : Nat) (hmn : m ≤ n) (x : X.Cell n),
      f.map m (downSrc X m n hmn x) = downSrc Y m n hmn (f.map n x) := by
  intro m n hmn x
  induction n generalizing m with
  | zero =>
      have hm : m = 0 := Nat.eq_zero_of_le_zero hmn
      subst hm
      simp [downSrc]
  | succ n ih =>
      by_cases hmne : m = n.succ
      · subst hmne
        simp [downSrc]
      · have hm' : m ≤ n := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hmn hmne)
        -- Unfold the single `downSrc` step (since `m ≠ n+1`), then apply IH to `X.src x`.
        simp [downSrc, hmne]
        refine (ih (m := m) (hmn := hm') (x := X.src x)).trans ?_
        -- Push `f` through the top `src` boundary.
        exact congrArg (downSrc Y m n hm') (f.map_src n x)

/-- A globular-set morphism commutes with `downTgt`. -/
theorem Hom.map_downTgt {X Y : GlobularSet.{u}} (f : X ⟶ Y) :
    ∀ (m n : Nat) (hmn : m ≤ n) (x : X.Cell n),
      f.map m (downTgt X m n hmn x) = downTgt Y m n hmn (f.map n x) := by
  intro m n hmn x
  induction n generalizing m with
  | zero =>
      have hm : m = 0 := Nat.eq_zero_of_le_zero hmn
      subst hm
      simp [downTgt]
  | succ n ih =>
      by_cases hmne : m = n.succ
      · subst hmne
        simp [downTgt]
      · have hm' : m ≤ n := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hmn hmne)
        simp [downTgt, hmne]
        refine (ih (m := m) (hmn := hm') (x := X.tgt x)).trans ?_
        exact congrArg (downTgt Y m n hm') (f.map_tgt n x)

/-- Structured globular sets as presheaves on `GlobularIndex`. -/
def toPresheafFunctor : GlobularSet.{u} ⥤ GlobularSetPsh.{u} where
  obj X := X.toPresheaf
  map {X Y} f :=
    { app := fun a x => f.map a.unop.n x
      naturality := by
        intro a b g
        funext x
        cases hg : g.unop with
        | mk kind valid =>
            cases kind with
            | none =>
                -- Identity case: `toPresheafMap` is definitional transport, which commutes with levelwise maps.
                cases a with
                | op a0 =>
                    cases b with
                    | op b0 =>
                        cases valid
                        simp [GlobularSet.toPresheaf, GlobularSet.toPresheafMap, hg]
            | some choice =>
                cases choice with
                | false =>
                    have h :=
                      Hom.map_downSrc (f := f)
                        (m := b.unop.n) (n := a.unop.n) (hmn := Nat.le_of_lt valid) (x := x)
                    simp [GlobularSet.toPresheaf, GlobularSet.toPresheafMap, hg] at *
                    exact h
                | true =>
                    have h :=
                      Hom.map_downTgt (f := f)
                        (m := b.unop.n) (n := a.unop.n) (hmn := Nat.le_of_lt valid) (x := x)
                    simp [GlobularSet.toPresheaf, GlobularSet.toPresheafMap, hg] at *
                    exact h }
  map_id := by
    intro X
    ext a x
    rfl
  map_comp := by
    intro X Y Z f g
    ext a x
    rfl

end GlobularSet

namespace GlobularSetPsh

/-- Presheaf globular sets as the minimal structured `GlobularSet` record. -/
def toGlobularSetFunctor : GlobularSetPsh.{u} ⥤ GlobularSet.{u} where
  obj X := X.toGlobularSet
  map {X Y} η :=
    { map := fun n x => η.app (Opposite.op (GlobularIndex.ofNat n)) x
      map_src := by
        intro n x
        have h := congrArg (fun f => f x) (η.naturality (GlobularIndex.src n).op)
        simpa [GlobularSetPsh.toGlobularSet, Function.comp] using h
      map_tgt := by
        intro n x
        have h := congrArg (fun f => f x) (η.naturality (GlobularIndex.tgt n).op)
        simpa [GlobularSetPsh.toGlobularSet, Function.comp] using h }
  map_id := by
    intro X
    apply GlobularSet.Hom.ext
    intro n x
    rfl
  map_comp := by
    intro X Y Z f g
    apply GlobularSet.Hom.ext
    intro n x
    rfl

end GlobularSetPsh

/-- The legacy structured `GlobularSet` category is equivalent to presheaf globular sets on `GlobularIndex`. -/
def globularSetEquivalence : GlobularSet.{u} ≌ GlobularSetPsh.{u} where
  functor := GlobularSet.toPresheafFunctor
  inverse := GlobularSetPsh.toGlobularSetFunctor
  unitIso := by
    refine NatIso.ofComponents (fun X => (GlobularSet.toPresheaf_toGlobularSetIso (X := X)).symm) ?_
    intro X Y f
    apply GlobularSet.Hom.ext
    intro n x
    rfl
  counitIso := by
    refine NatIso.ofComponents (fun X => GlobularSetPsh.toGlobularSet_toPresheafIso (X := X)) ?_
    intro X Y f
    ext a x
    rfl
  functor_unitIso_comp := by
    intro X
    ext a x
    rfl

end IteratedVirtual
end HeytingLean
