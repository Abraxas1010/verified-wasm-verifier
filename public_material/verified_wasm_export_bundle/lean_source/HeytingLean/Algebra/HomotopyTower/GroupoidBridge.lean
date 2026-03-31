import Mathlib.CategoryTheory.Category.Quiv
import HeytingLean.Algebra.HomotopyTower.CategoryBridge
import HeytingLean.LoF.Combinators.Category.Groupoid
import HeytingLean.LoF.Combinators.Category.OmegaTowerLimitGroupoid

namespace HeytingLean
namespace Algebra
namespace HomotopyTower

open CategoryTheory
open HeytingLean.LoF.Combinators.Category

universe u

variable {α : Type u} [Order.Frame α]

/-- A functorial quiver-valued transport surface to be attached to a stabilized tower. -/
structure StableTransportQuiver (T : NucleusTower (α := α)) (hfin : FiniteImage T) where
  Obj : Nat → Type u
  instQuiver : ∀ n, Quiver (Obj n)
  drop : ∀ n, Obj (n + 1) ⥤q Obj n

attribute [instance] StableTransportQuiver.instQuiver

/-- Stagewise free groupoid on the transport quiver. -/
abbrev StageGroupoid {T : NucleusTower (α := α)} {hfin : FiniteImage T}
    (Q : StableTransportQuiver T hfin) (n : Nat) : Type u :=
  Quiver.FreeGroupoid (Q.Obj n)

/-- The quiver prefunctor induces a functor between stagewise free groupoids. -/
noncomputable def dropStageGroupoid {T : NucleusTower (α := α)} {hfin : FiniteImage T}
    (Q : StableTransportQuiver T hfin) :
    ∀ n, StageGroupoid Q (n + 1) ⥤ StageGroupoid Q n :=
  fun n => Quiver.freeGroupoidFunctor (Q.drop n)

/-- The resulting tower of stagewise free groupoids. -/
noncomputable def stableGroupoidTower {T : NucleusTower (α := α)} {hfin : FiniteImage T}
    (Q : StableTransportQuiver T hfin) : CatTower where
  Obj := StageGroupoid Q
  inst := fun _ => by infer_instance
  drop := dropStageGroupoid Q

/-- The inverse-limit type of the stagewise groupoid tower. -/
abbrev stableGroupoidLimit {T : NucleusTower (α := α)} {hfin : FiniteImage T}
    (Q : StableTransportQuiver T hfin) : Type u :=
  TowerLimit (stableGroupoidTower Q)

noncomputable instance {T : NucleusTower (α := α)} {hfin : FiniteImage T}
    (Q : StableTransportQuiver T hfin) : Groupoid (stableGroupoidLimit Q) := by
  dsimp [stableGroupoidLimit, stableGroupoidTower]
  infer_instance

end HomotopyTower
end Algebra
end HeytingLean
