import HeytingLean.LoF.Nucleus
import HeytingLean.LoF.OmegaCategory
import HeytingLean.LoF.Rosetta.Core
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Monoidal.Cartesian.InfSemilattice

/-
# Rosetta.LensBridges: lens-level Baez–Stay models over `Ω_R`

This module packages a lightweight categorical interface for lenses sitting
over a reentry nucleus `R`.  The core idea is that each such lens should
transport the Baez–Stay closed symmetric monoidal structure on `Ω_R` to some
target category of “observables” while preserving the round-trip law.

To keep the implementation fully total and warning-free, we provide:

* a `LensModel` structure recording `R`, a target `Obj`, functors
  `encode : Ω_R ⥤ Obj` and `decode : Obj ⥤ Ω_R`, and a round-trip natural
  isomorphism `decode ⋙ encode ≅ 𝟭 Ω_R`;
* a canonical identity instance `identityLensModel` with `Obj := Ω_R`,
  where all categorical structure is inherited from `OmegaCategory`.

Concrete lenses such as the graph, geometric, tensor, or Clifford bridges can
instantiate this structure in future extensions, using their existing
`RoundTrip` contracts to build the corresponding functors and isomorphisms.
-/

namespace HeytingLean
namespace LoF
namespace Rosetta

open CategoryTheory

universe u v

variable {α : Type u} [PrimaryAlgebra α]

/-- A Rosetta lens model over a reentry nucleus `R`.

The target `Obj` carries a categorical and monoidal structure, and we have
functors `encode`/`decode` between `Ω_R` and `Obj` whose composite back to
`Ω_R` is naturally isomorphic to the identity.  This is the lens-level
abstraction for “stay monoidal” transports of Ω-structure. -/
structure LensModel where
  (R : Reentry α)
  (Obj : Type v)
  [cat : Category Obj]
  [monoidal : MonoidalCategory Obj]
  (encode : R.Omega ⥤ Obj)
  (decode : Obj ⥤ R.Omega)
  (round : encode ⋙ decode ≅ 𝟭 (R.Omega))

attribute [instance] LensModel.cat LensModel.monoidal

/-- Canonical Rosetta lens model with target `Ω_R` itself.

Here the encode/decode functors are both the identity on `Ω_R`, and the
round-trip is witnessed by the identity natural isomorphism.  This gives a
fully worked example of a `LensModel` using only the categorical structure
already installed in `OmegaCategory`. -/
noncomputable def identityLensModel (R : Reentry α) : LensModel (α := α) where
  R := R
  Obj := R.Omega
  cat := inferInstance
  monoidal := inferInstance
  encode := 𝟭 _
  decode := 𝟭 _
  round := Iso.refl _

end Rosetta
end LoF
end HeytingLean
