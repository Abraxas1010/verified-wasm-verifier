import HeytingLean.Topos.LocSys.ExternalTensor

import Mathlib.CategoryTheory.Functor.Const
import Mathlib.GroupTheory.Perm.Fin

namespace HeytingLean
namespace Topos
namespace LocSys

open CategoryTheory
open scoped MonoidalCategory

universe uK uB vB

variable (K : Type uK) [CommRing K]

namespace Examples
namespace BGReps

/-- Constant local system on a base groupoid. -/
abbrev const (X : Grpd.{vB, uB}) (V : Coeff K) : LocalSystem (K := K) X :=
  (Functor.const X).obj V

/-- A minimal “trivial representation” example: a `BG`-local system constant at `𝟙_`. -/
noncomputable abbrev trivial (G : Type vB) [Group G] : LocalSystem (K := K) (Base1.BG G) :=
  const (K := K) (X := Base1.BG G) (𝟙_ (Coeff K))

/-- A `G = S₂` (permutations of two points) action on the 1-dimensional `K`-module by `±𝟙`. -/
noncomputable def signEndPermFin2 : (Equiv.Perm (Fin 2)) →* End (ModuleCat.of K K) where
  toFun g := if g = 1 then (1 : End (ModuleCat.of K K)) else -(1 : End (ModuleCat.of K K))
  map_one' := by
    simp
  map_mul' := by
    classical
    intro g h
    fin_cases g <;> fin_cases h <;> simp

/--
A nontrivial `BG`-local system: the sign representation of `S₂ = Equiv.Perm (Fin 2)` on the
1-dimensional `K`-module.
-/
noncomputable def signPermFin2 : LocalSystem (K := K) (Base1.BG (G := Equiv.Perm (Fin 2))) :=
  CategoryTheory.SingleObj.functor (C := Coeff K) (X := ModuleCat.of K K) (signEndPermFin2 (K := K))

end BGReps
end Examples

end LocSys
end Topos
end HeytingLean
