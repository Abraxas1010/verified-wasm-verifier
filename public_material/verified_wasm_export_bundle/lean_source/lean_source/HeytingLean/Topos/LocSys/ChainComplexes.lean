import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.AlgebraicTopology.SimplicialObject.Basic

namespace HeytingLean
namespace Topos
namespace LocSys

open CategoryTheory

universe u

/-- Coefficient category for `K`-linear local systems (v1): plain `K`-modules. -/
abbrev Coeff (K : Type u) [CommRing K] :=
  ModuleCat K

/-- Future coefficient category: `ℕ`-indexed chain complexes of `K`-modules. -/
abbrev ComplexCoeff (K : Type u) [CommRing K] :=
  ChainComplex (ModuleCat K) ℕ

/-- A simplicial object in the coefficient category (paper: "simplicial chain complexes"). -/
abbrev SimpCoeff (K : Type u) [CommRing K] :=
  SimplicialObject (Coeff K)

end LocSys
end Topos
end HeytingLean
