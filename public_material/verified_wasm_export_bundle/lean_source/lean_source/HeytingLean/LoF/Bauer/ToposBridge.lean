import HeytingLean.Topos.LocalOperator
import Mathlib.CategoryTheory.Subobject.Types
import Mathlib.CategoryTheory.Limits.Types.Shapes
import Mathlib.Order.Nucleus

/-!
# Bauer ↔ Topos: nuclei on `Prop` induce local operators on `Type`

This module implements the Bauer “Phase 3” bridge:

* start from a nucleus `J : Nucleus Prop` (a Lawvere–Tierney style closure on truth values),
* close subobjects of a type `X` by applying `J` pointwise to their membership predicates, and
* package the resulting pullback-stable family of closures as a
  `HeytingLean.Topos.LocalOperator (Type u)`.

Compared to earlier scaffolding, this version is intentionally *set-level* for `Type u`:
we use `Types.subobjectEquivSet` to view `Subobject X` as `Set X`, and transport the closure
operator along that order isomorphism.
-/

namespace HeytingLean
namespace LoF
namespace Bauer

open CategoryTheory
open CategoryTheory.Limits

universe u

attribute [local instance] subtype_val_mono

namespace ToposBridge

/-! ## Sets, closures, and transport along `Types.subobjectEquivSet` -/

lemma range_mk_arrow {A X : Type u} (i : A ⟶ X) [Mono i] :
    Set.range (Subobject.mk i).arrow = Set.range i := by
  classical
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨(Subobject.underlyingIso i).hom a, ?_⟩
    have h := congrArg (fun f => f a) (Subobject.underlyingIso_hom_comp_eq_mk (f := i))
    simpa using h
  · rintro ⟨a, rfl⟩
    refine ⟨(Subobject.underlyingIso i).inv a, ?_⟩
    have h := congrArg (fun f => f a) (Subobject.underlyingIso_arrow (f := i))
    simpa using h

/-- View a `Subobject X` (in `Type`) as a subset of `X`. -/
noncomputable abbrev asSet {X : Type u} (S : Subobject X) : Set X :=
  Types.subobjectEquivSet X S

/-- In `Type`, `Types.subobjectEquivSet` is the range of the chosen representative arrow. -/
lemma asSet_eq_range_arrow {X : Type u} (S : Subobject X) :
    asSet (X := X) S = Set.range S.arrow := by
  classical
  -- Unfold through the construction: ThinSkeleton representative → `Set.range`,
  -- and then unfold `Subobject.arrow` to see it uses the same representative.
  simp [asSet, Types.subobjectEquivSet, Types.monoOverEquivalenceSet,
    CategoryTheory.Equivalence.thinSkeletonOrderIso, Subobject.arrow,
    Subobject.representative, Subobject.equivMonoOver]

/-- Close a subset `S : Set X` by applying `J` pointwise to membership. -/
def closeSet (J : Nucleus Prop) {X : Type u} (S : Set X) : Set X :=
  {x : X | J (x ∈ S)}

lemma closeSet_inf (J : Nucleus Prop) {X : Type u} (A B : Set X) :
    closeSet (J := J) (A ∩ B) = closeSet (J := J) A ∩ closeSet (J := J) B := by
  ext x
  -- `J.map_inf` is an equality on `Prop`; rewrite it as an `↔`.
  refine iff_of_eq ?_
  simpa [closeSet, Set.mem_inter_iff] using (J.map_inf (x := (x ∈ A)) (y := (x ∈ B)))

/-- The pointwise-membership closure as a closure operator on `Set X`. -/
noncomputable def closeSetClosure (J : Nucleus Prop) (X : Type u) : ClosureOperator (Set X) :=
  ClosureOperator.mk₂ (closeSet (J := J) (X := X))
    (fun S => by
      intro x hx
      exact (J.le_apply (x := (x ∈ S))) hx)
    (fun {A B} hAB => by
      intro x hx
      -- `hx : J (x ∈ A)` and `hAB : A ⊆ {y | J (y ∈ B)}`.
      have hImp : (x ∈ A) ≤ J (x ∈ B) := by
        intro hxA
        exact hAB hxA
      have hx' : J (x ∈ A) ≤ J (J (x ∈ B)) := J.monotone hImp
      have hx'' : J (x ∈ A) ≤ J (x ∈ B) := by
        simpa [J.idempotent (x := (x ∈ B))] using hx'
      exact hx'' hx)

/-- The induced closure operator on `Subobject X`, transported along `Types.subobjectEquivSet`. -/
noncomputable def closeSubobjectClosure (J : Nucleus Prop) (X : Type u) :
    ClosureOperator (Subobject X) :=
  (closeSetClosure (J := J) X).conjBy (Types.subobjectEquivSet X).symm

/-- Close a subobject `S ⊆ X` by applying a nucleus `J : Nucleus Prop` pointwise to membership. -/
noncomputable def closeSubobject (J : Nucleus Prop) {X : Type u} (S : Subobject X) : Subobject X :=
  closeSubobjectClosure (J := J) X S

@[simp] lemma asSet_closeSubobject (J : Nucleus Prop) {X : Type u} (S : Subobject X) :
    asSet (closeSubobject (X := X) J S) = closeSet (J := J) (asSet S) := by
  -- Transport to `Set X` and cancel the `subobjectEquivSet`/`.symm` pair.
  simp [asSet, closeSubobject, closeSubobjectClosure, closeSetClosure, closeSet]

/-! ## Pullback stability in `Type` -/

lemma range_pullback_snd {A X Y : Type u} (i : A ⟶ X) (f : Y ⟶ X) :
    Set.range (pullback.snd i f) = {y : Y | ∃ a : A, i a = f y} := by
  ext y
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨pullback.fst i f p, ?_⟩
    exact congrArg (fun h => h p) (pullback.condition (f := i) (g := f))
  · rintro ⟨a, ha⟩
    let x : Types.PullbackObj i f := ⟨⟨a, y⟩, ha⟩
    refine ⟨(Types.pullbackIsoPullback i f).inv x, ?_⟩
    simp [x]

lemma asSet_pullback {X Y : Type u} (f : Y ⟶ X) (S : Subobject X) :
    asSet ((Subobject.pullback f).obj S) = {y : Y | f y ∈ asSet S} := by
  classical
  -- Rewrite `pullback` as an explicit `mk` in `Type`, then compute ranges.
  have hs : (Subobject.pullback f).obj S = Subobject.mk (pullback.snd S.arrow f) := by
    simpa using (Subobject.pullback_obj (f := f) (x := S))
  calc
    asSet ((Subobject.pullback f).obj S)
        = asSet (Subobject.mk (pullback.snd S.arrow f)) := by simp [hs]
    _   = Set.range (pullback.snd S.arrow f) := by
            -- `asSet` of a `mk` is range of the `mk` arrow, which has the same range as the original mono.
            have h := asSet_eq_range_arrow (X := Y) (S := Subobject.mk (pullback.snd S.arrow f))
            simpa [range_mk_arrow (i := pullback.snd S.arrow f)] using h
    _   = {y : Y | ∃ a : (S : Type u), S.arrow a = f y} := by
            simpa using (range_pullback_snd (i := S.arrow) (f := f))
    _   = {y : Y | f y ∈ Set.range S.arrow} := by
            ext y; rfl
    _   = {y : Y | f y ∈ asSet S} := by
            simp [asSet_eq_range_arrow]

lemma pullback_closeSubobject (J : Nucleus Prop) {X Y : Type u} (f : Y ⟶ X) (S : Subobject X) :
    (Subobject.pullback f).obj (closeSubobject (X := X) J S)
      = closeSubobject (X := Y) J ((Subobject.pullback f).obj S) := by
  -- Prove by comparing underlying subsets of `Y`.
  apply (Types.subobjectEquivSet Y).injective
  ext y
  simp [asSet_pullback, asSet_closeSubobject, closeSet]

/-! ## Meet preservation -/

lemma closeSubobject_inf (J : Nucleus Prop) {X : Type u} (S T : Subobject X) :
    closeSubobject (X := X) J (S ⊓ T)
      = closeSubobject (X := X) J S ⊓ closeSubobject (X := X) J T := by
  apply (Types.subobjectEquivSet X).injective
  -- Use that the order iso preserves infimum.
  have hInf : asSet (S ⊓ T) = asSet S ∩ asSet T := by
    -- `asSet` is just `Types.subobjectEquivSet`.
    dsimp [asSet]
    exact (OrderIso.map_inf (Types.subobjectEquivSet X) S T)
  ext x
  simp [asSet_closeSubobject, hInf, closeSet_inf]

end ToposBridge

/-! ## Packaging as a `Topos.LocalOperator` -/

/-- A nucleus on truth values (`Prop`) induces a pullback-stable closure operator on subobjects
of every type, i.e. a `HeytingLean.Topos.LocalOperator` on `Type u`. -/
noncomputable def localOperatorOfPropNucleus (J : Nucleus Prop) :
    HeytingLean.Topos.LocalOperator (Type u) :=
  { cl := fun X => ToposBridge.closeSubobjectClosure (J := J) X
    pullback_stable := by
      intro X Y f S
      simpa [ToposBridge.closeSubobject, ToposBridge.closeSubobjectClosure]
        using (ToposBridge.pullback_closeSubobject (J := J) (f := f) S) }

theorem localOperatorOfPropNucleus_meetPreserving (J : Nucleus Prop) :
    HeytingLean.Topos.LocalOperator.MeetPreserving (localOperatorOfPropNucleus (J := J)) :=
  { map_inf := by
      intro X S T
      -- Expand the closure on `Subobject X` and reuse `closeSubobject_inf`.
      simpa [localOperatorOfPropNucleus, ToposBridge.closeSubobject, ToposBridge.closeSubobjectClosure]
        using (ToposBridge.closeSubobject_inf (J := J) (S := S) (T := T)) }

end Bauer
end LoF
end HeytingLean
