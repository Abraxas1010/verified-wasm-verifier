import Mathlib.CategoryTheory.Category.Basic
import HeytingLean.Quantum.VacuumOmegaR
import HeytingLean.Quantum.OMLCat
import HeytingLean.Quantum.QGIContext
import HeytingLean.LoF.HeytingCat
import HeytingLean.LoF.HeytingCore

/-
# Vacuum contexts as a category and the Ωᴿ functor

This module provides the categorical skeleton used in the Direction 6
“vacuum naturality” plan:

* `VacuumObj` bundles a `VacuumOmegaRContext` together with its
  orthomodular and primary-algebra structure.
* `VacuumCat` is the category of such objects.
* `ForgetVacuumToOML` projects a vacuum object to its OML carrier.
* `ForgetVacuumToHeyt` projects a vacuum object to its Ωᴿ Heyting core.
* `QLFunctor` is the Ωᴿ translation functor, currently defined on
  `VacuumCat` (contexts).  An OML-level variant would require an
  additional choice assigning a context to each bare OML and is left
  for a later extension.
-/

namespace HeytingLean
namespace Quantum

open CategoryTheory
open HeytingLean.Quantum
open HeytingLean.Quantum.OML
open HeytingLean.Quantum.OMLCat
open HeytingLean.LoF

universe u

/-- Bundled vacuum context: an orthomodular lattice `β`, a primary algebra
`α`, and a `VacuumOmegaRContext β α` witnessing the vacuum ↔ Ωᴿ bridge on
these carriers. -/
structure VacuumObj where
  β : Type u
  α : Type u
  [orthocomplβ : OrthocomplementedLattice β]
  [orthomodβ   : OrthomodularLattice β]
  [primaryα    : PrimaryAlgebra α]
  C : VacuumOmegaRContext β α

attribute [instance] VacuumObj.orthocomplβ
attribute [instance] VacuumObj.orthomodβ
attribute [instance] VacuumObj.primaryα

namespace VacuumObj

instance : CoeSort VacuumObj (Type u) :=
  ⟨fun X => X.β⟩

end VacuumObj

/-- The category of vacuum contexts. Objects are `VacuumObj`, morphisms
are defined in `VacuumCat.Hom`. -/
abbrev VacuumCat := VacuumObj

namespace VacuumCat

/-- Morphisms between vacuum contexts: an orthomodular-lattice hom on the
`β` layer together with a Heyting hom on the Ωᴿ cores.  Compatibility
conditions between these components (e.g. preservation of the vacuum image)
will be added in later naturality theorems. -/
@[ext]
structure Hom (X Y : VacuumCat.{u}) where
  /-- OML-level morphism between the underlying lattices. -/
  fβ : OMLCat.of X.β ⟶ OMLCat.of Y.β
  /-- Ωᴿ-level morphism between the Heyting cores. -/
  fΩ :
    HeytAlg.of X.C.R.Omega ⟶ HeytAlg.of Y.C.R.Omega

/-- Identity morphism on a vacuum context. -/
def id (X : VacuumCat.{u}) : Hom X X where
  fβ := 𝟙 (OMLCat.of X.β)
  fΩ := 𝟙 (HeytAlg.of X.C.R.Omega)

/-- Composition of vacuum-context morphisms, defined componentwise using
the existing categorical structure on `OMLCat` and `HeytAlg`. -/
def comp {X Y Z : VacuumCat} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  fβ := f.fβ ≫ g.fβ
  fΩ := f.fΩ ≫ g.fΩ

@[simp] lemma id_fβ (X : VacuumCat) :
    (id X).fβ = 𝟙 (OMLCat.of X.β) := rfl

@[simp] lemma id_fΩ (X : VacuumCat) :
    (id X).fΩ = 𝟙 (HeytAlg.of X.C.R.Omega) := rfl

@[simp] lemma comp_fβ {X Y Z : VacuumCat}
    (f : Hom X Y) (g : Hom Y Z) :
    (comp f g).fβ = f.fβ ≫ g.fβ := rfl

@[simp] lemma comp_fΩ {X Y Z : VacuumCat}
    (f : Hom X Y) (g : Hom Y Z) :
    (comp f g).fΩ = f.fΩ ≫ g.fΩ := rfl

instance : Category VacuumCat where
  Hom X Y := Hom X Y
  id X := id X
  comp f g := comp f g
  id_comp := by
    intro X Y f
    ext <;> simp [comp, id, Category.id_comp]
  comp_id := by
    intro X Y f
    ext <;> simp [comp, id, Category.comp_id]
  assoc := by
    intro W X Y Z f g h
    ext <;> simp [comp, Category.assoc]

/-- Forget the vacuum data and keep only the OML carrier. -/
def ForgetVacuumToOML : VacuumCat ⥤ OMLCat where
  obj X := OMLCat.of X.β
  map {X Y} (f : Hom X Y) := f.fβ
  map_id X := rfl
  map_comp f g := rfl

/-- Forget the OML data and keep only the Ωᴿ Heyting core. -/
def ForgetVacuumToHeyt : VacuumCat ⥤ LoF.HeytingCat where
  obj X := HeytAlg.of X.C.R.Omega
  map {X Y} (f : Hom X Y) := f.fΩ
  map_id X := rfl
  map_comp f g := rfl

/-- The Ωᴿ translation functor, sending a vacuum context to the Heyting
algebra carried by its fixed-point core.  This is the categorical version
of the `VacuumOmegaRContext` bridge. -/
abbrev QLFunctor : VacuumCat ⥤ LoF.HeytingCat :=
  ForgetVacuumToHeyt

/-- Underlying Ωᴿ carrier associated to a vacuum context. -/
abbrev OmegaCarrier (X : VacuumCat) : Type u :=
  X.C.R.Omega

/-- Ωᴿ-level action of a vacuum-context morphism on the carriers. -/
def OmegaMap {X Y : VacuumCat} (f : Hom X Y) :
    OmegaCarrier X → OmegaCarrier Y :=
  fun x => f.fΩ x

/-- Distinguished vacuum element in the Ωᴿ carrier of a context. -/
def vacuumAt (X : VacuumCat) : OmegaCarrier X :=
  X.C.vacuumOmega

/-- Compatibility predicate: a morphism is vacuum-compatible if it sends
the Ωᴿ vacuum of the source to that of the target. -/
def VacuumCompatible {X Y : VacuumCat} (f : Hom X Y) : Prop :=
  OmegaMap f (vacuumAt X) = vacuumAt Y

/-- Naturality of the vacuum element along a vacuum-compatible morphism. -/
lemma vacuum_natural {X Y : VacuumCat} (f : Hom X Y)
    (h : VacuumCompatible f) :
    OmegaMap f (vacuumAt X) = vacuumAt Y :=
  h

/-- A vacuum morphism is a context morphism together with the proof that
    it preserves the distinguished Ωᴿ vacuum. This is the data needed to
    state naturality properties for both the vacuum and the Euler
    boundary. -/
structure VacuumMor (X Y : VacuumCat) where
  hom : Hom X Y
  vacuum_compatible : VacuumCompatible hom

/-- Euler boundary in the Ωᴿ carrier of a context. -/
noncomputable def eulerAt (X : VacuumCat) : OmegaCarrier X :=
  X.C.R.eulerBoundary

/-- At each context, the Ωᴿ vacuum coincides with the Euler boundary. -/
lemma vacuumAt_eq_eulerAt (X : VacuumCat) :
    vacuumAt X = eulerAt X := by
  -- This is just `vacuumOmega_eq_eulerBoundary` specialised to `X.C`.
  have h :=
    Quantum.VacuumOmegaRContext.vacuumOmega_eq_eulerBoundary (C := X.C)
  simpa [vacuumAt, eulerAt] using h

/-- Naturality of the Euler boundary along a vacuum morphism: the Ωᴿ map
    carries the Euler boundary of the source context to that of the
    target context. -/
lemma VacuumMor.euler_natural {X Y : VacuumCat} (ϕ : VacuumMor X Y) :
    OmegaMap ϕ.hom (eulerAt X) = eulerAt Y := by
  -- Rewrite both Euler boundaries via the corresponding vacua and use
  -- `VacuumMor.vacuum_natural`.
  have hX : eulerAt X = vacuumAt X :=
    (vacuumAt_eq_eulerAt (X := X)).symm
  have hY : vacuumAt Y = eulerAt Y :=
    vacuumAt_eq_eulerAt (X := Y)
  calc
    OmegaMap ϕ.hom (eulerAt X)
        = OmegaMap ϕ.hom (vacuumAt X) := by
            simpa [OmegaMap, hX]
    _   = vacuumAt Y :=
            ϕ.vacuum_compatible
    _   = eulerAt Y := by
            simpa [hY]

/-- Concrete QGI vacuum object, obtained from `QGIContext.qgiBaseContext`. -/
noncomputable def qgiObj : VacuumObj :=
  { β := QGIContext.β
    α := QGIContext.α
    C := QGIContext.qgiBaseContext }

/-- In the QGI example, the general Euler-boundary equality reduces to
    the base-context instance of `vacuumOmega_eq_eulerBoundary`. -/
lemma qgi_euler_agrees :
    qgiObj.C.vacuumOmega = qgiObj.C.R.eulerBoundary := by
  simpa [qgiObj] using
    Quantum.VacuumOmegaRContext.vacuumOmega_eq_eulerBoundary
      (C := QGIContext.qgiBaseContext)

end VacuumCat

end Quantum
end HeytingLean
