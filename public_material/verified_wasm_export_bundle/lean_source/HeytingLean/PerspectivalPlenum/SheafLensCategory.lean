import HeytingLean.PerspectivalPlenum.Lens.Collapse
import HeytingLean.PerspectivalPlenum.Lens.Examples.SquareCircle
import HeytingLean.Topos.LTfromNucleus
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Types.Basic

namespace HeytingLean
namespace PerspectivalPlenum
namespace LensSheaf

open CategoryTheory

universe u v

/-- Bundled semantic-lens objects. -/
structure LensObj (A : Type u) where
  lens : Lens.SemanticLens A

/-- Morphisms pull witness/contradiction judgments back along a map. -/
structure LensHom {A : Type u} (X Y : LensObj A) where
  map : A → A
  pullWitness : ∀ {x : A}, Y.lens.witness x → X.lens.witness (map x)
  pullContradicts : ∀ {x : A}, Y.lens.contradicts x → X.lens.contradicts (map x)

@[ext] theorem LensHom.ext {A : Type u} {X Y : LensObj A}
    {f g : LensHom X Y} (hmap : f.map = g.map) : f = g := by
  cases f
  cases g
  cases hmap
  simp

instance lensCategory (A : Type u) : Category (LensObj A) where
  Hom X Y := LensHom X Y
  id X :=
    { map := id
      pullWitness := by
        intro x hx
        simpa using hx
      pullContradicts := by
        intro x hx
        simpa using hx }
  comp f g :=
    { map := f.map ∘ g.map
      pullWitness := by
        intro x hx
        exact f.pullWitness (g.pullWitness hx)
      pullContradicts := by
        intro x hx
        exact f.pullContradicts (g.pullContradicts hx) }
  id_comp := by
    intro X Y f
    ext x
    rfl
  comp_id := by
    intro X Y f
    ext x
    rfl
  assoc := by
    intro W X Y Z f g h
    ext x
    rfl

/-- Presheaves over the lens category. -/
abbrev LensPresheaf (A : Type u) := Functor (Opposite (LensObj A)) (Type u)

/-- A covering family of a lens object. -/
structure CoveringFamily {A : Type u} (U : LensObj A) where
  I : Type v
  obj : I → LensObj A
  hom : ∀ i : I, obj i ⟶ U

/--
Coverage package that aligns a lens-site view with a Lawvere-Tierney kit.
This keeps the bridge from lens covers to local-operator semantics explicit.
-/
structure LensSiteCoverage
    (A : Type u)
    (C : Type v) [Category.{v} C]
    [CategoryTheory.Limits.HasPullbacks C] [CategoryTheory.HasClassifier C] where
  ltKit : HeytingLean.Topos.LTfromNucleus.LawvereTierneyKit (C := C)
  cover : (U : LensObj A) → CoveringFamily U

namespace LensSiteCoverage

noncomputable def toLocalOperator
    {A : Type u}
    {C : Type v} [Category.{v} C]
    [CategoryTheory.Limits.HasPullbacks C] [CategoryTheory.HasClassifier C]
    (S : LensSiteCoverage A C) : HeytingLean.Topos.LocalOperator C :=
  HeytingLean.Topos.LTfromNucleus.ofLawvereTierneyKit (C := C) S.ltKit

end LensSiteCoverage

/-- Sections over a cover, one per member object. -/
structure MatchingFamily {A : Type u}
    (F : LensPresheaf A) (U : LensObj A) (C : CoveringFamily U) where
  sec : ∀ i : C.I, F.obj (Opposite.op (C.obj i))

/-- A matching family amalgamates when it descends from a section on `U`. -/
def Amalgamates {A : Type u}
    (F : LensPresheaf A) (U : LensObj A) (C : CoveringFamily U)
    (m : MatchingFamily F U C) : Prop :=
  ∃ s : F.obj (Opposite.op U),
    ∀ i : C.I, F.map (Quiver.Hom.op (C.hom i)) s = m.sec i

/-- Minimal sheaf condition over lens covers (existence only). -/
structure IsLensSheaf {A : Type u} (F : LensPresheaf A) : Prop where
  amalgamate :
    ∀ (U : LensObj A) (C : CoveringFamily U) (m : MatchingFamily F U C),
      Amalgamates F U C m

/-- Data-level sheafification pathway for lens semantics. -/
structure SheafificationPath {A : Type u} (F : LensPresheaf A) where
  sheafObj : LensPresheaf A
  isSheaf : IsLensSheaf sheafObj
  unit : F ⟶ sheafObj
  lift : ∀ {G : LensPresheaf A}, IsLensSheaf G → (F ⟶ G) → (sheafObj ⟶ G)
  fac : ∀ {G : LensPresheaf A} (hG : IsLensSheaf G) (eta : F ⟶ G),
      unit ≫ lift hG eta = eta

/-- Witness-only local sections for a lens object. -/
def WitnessSection {A : Type u} (X : LensObj A) : Type u :=
  {x : A // X.lens.witness x}

/-- Canonical presheaf that transports witness sections along lens morphisms. -/
def witnessPresheaf (A : Type u) : LensPresheaf A where
  obj U := WitnessSection (Opposite.unop U)
  map := by
    intro U V f sx
    let h : Opposite.unop V ⟶ Opposite.unop U := Opposite.unop f
    exact ⟨h.map sx.1, h.pullWitness sx.2⟩
  map_id := by
    intro U
    funext sx
    rfl
  map_comp := by
    intro U V W f g
    funext sx
    rfl

/-- Singleton cover used for concrete gluing examples. -/
def singletonCover {A : Type u} (U : LensObj A) : CoveringFamily U where
  I := PUnit
  obj _ := U
  hom _ := 𝟙 U

/-- Two-member cover (for non-singleton gluing tests). -/
def pairCover {A : Type u} (U : LensObj A) : CoveringFamily U where
  I := Bool
  obj _ := U
  hom _ := 𝟙 U

/-- Witness presheaf glues every singleton matching family. -/
theorem witnessPresheaf_singleton_amalgamates {A : Type u} (U : LensObj A)
    (m : MatchingFamily (witnessPresheaf A) U (singletonCover U)) :
    Amalgamates (witnessPresheaf A) U (singletonCover U) m := by
  refine ⟨m.sec PUnit.unit, ?_⟩
  intro i
  cases i
  simp [singletonCover]

/--
If the two local sections on a pair cover agree, the witness presheaf provides
an amalgamation on the shared base object.
-/
theorem witnessPresheaf_pair_amalgamates_of_eq {A : Type u} (U : LensObj A)
    (m : MatchingFamily (witnessPresheaf A) U (pairCover U))
    (hCompat : m.sec false = m.sec true) :
    Amalgamates (witnessPresheaf A) U (pairCover U) m := by
  refine ⟨m.sec false, ?_⟩
  intro i
  cases i <;> simp [pairCover, hCompat]

/--
Amalgamations for a fixed pair-cover matching family are unique when they exist.
This gives a concrete uniqueness witness for the non-singleton gluing shape.
-/
theorem witnessPresheaf_pair_amalgamation_unique {A : Type u} (U : LensObj A)
    (m : MatchingFamily (witnessPresheaf A) U (pairCover U))
    {s t : (witnessPresheaf A).obj (Opposite.op U)}
    (hs : ∀ i : Bool, (witnessPresheaf A).map (Quiver.Hom.op ((pairCover U).hom i)) s = m.sec i)
    (ht : ∀ i : Bool, (witnessPresheaf A).map (Quiver.Hom.op ((pairCover U).hom i)) t = m.sec i) :
    s = t := by
  have hs0 : s = m.sec false := by
    simpa [pairCover] using hs false
  have ht0 : t = m.sec false := by
    simpa [pairCover] using ht false
  exact hs0.trans ht0.symm

/-- Global/plenum-level existence means witnessability in at least one lens object. -/
def ExistsInPlenum {A : Type u} (x : A) : Prop :=
  ∃ X : LensObj A, X.lens.witness x

theorem existsInPlenum_of_localWitness {A : Type u} (X : LensObj A) {x : A}
    (hx : X.lens.witness x) : ExistsInPlenum x :=
  ⟨X, hx⟩

/--
Schema theorem: an object may exist in the plenum while collapsing in a strict lens.
This formalizes the intended global-vs-local perspective split.
-/
theorem existsInPlenum_and_localCollapse {A : Type u}
    (strict permissive : Lens.SemanticLens A) (x : A)
    (hStrict : ¬ Lens.allowsContradictions strict.profile)
    (hStrictWitness : strict.witness x)
    (hStrictContra : strict.contradicts x)
    (hPermWitness : permissive.witness x) :
    ExistsInPlenum x ∧ Lens.CollapseToBottom strict x := by
  refine ⟨existsInPlenum_of_localWitness ⟨permissive⟩ hPermWitness, ?_⟩
  exact Lens.collapse_of_strict_contradiction strict x hStrict hStrictWitness hStrictContra

namespace Examples

open Lens.Examples

abbrev ShapeWitnessPresheaf := witnessPresheaf ShapeObject

/-- Concrete lens objects from the square-circle development. -/
def euclideanObj : LensObj ShapeObject :=
  ⟨euclideanLens⟩

def higherDimObj : LensObj ShapeObject :=
  ⟨higherDimLens⟩

/-- Restriction from permissive lens to strict lens via identity on the carrier. -/
def higherToEuclidean : higherDimObj ⟶ euclideanObj :=
  { map := id
    pullWitness := by
      intro x hx
      simpa [euclideanLens, higherDimLens] using hx
    pullContradicts := by
      intro x hx
      simpa [euclideanLens, higherDimLens] using hx }

/-- A witness section for square-circle in the Euclidean object. -/
def squareCircleSection :
    ShapeWitnessPresheaf.obj (Opposite.op euclideanObj) := by
  change WitnessSection euclideanObj
  exact ⟨ShapeObject.squareCircle, by
    simp [euclideanObj, euclideanLens]⟩

/-- The same section viewed in the higher-dimensional object. -/
def squareCircleSectionHigher :
    ShapeWitnessPresheaf.obj (Opposite.op higherDimObj) := by
  change WitnessSection higherDimObj
  exact ⟨ShapeObject.squareCircle, by
    simp [higherDimObj, higherDimLens]⟩

/-- End-to-end restriction example in the lens presheaf. -/
example :
    ShapeWitnessPresheaf.map (Quiver.Hom.op higherToEuclidean) squareCircleSection
      = squareCircleSectionHigher := by
  apply Subtype.ext
  rfl

/-- Singleton matching family generated by the Euclidean square-circle section. -/
def euclideanSingletonFamily :
    MatchingFamily ShapeWitnessPresheaf euclideanObj (singletonCover euclideanObj) where
  sec _ := squareCircleSection

/-- The singleton family glues to a global Euclidean section. -/
theorem euclideanSingletonFamily_glues :
    Amalgamates ShapeWitnessPresheaf euclideanObj (singletonCover euclideanObj)
      euclideanSingletonFamily :=
  witnessPresheaf_singleton_amalgamates euclideanObj euclideanSingletonFamily

end Examples

end LensSheaf
end PerspectivalPlenum
end HeytingLean
