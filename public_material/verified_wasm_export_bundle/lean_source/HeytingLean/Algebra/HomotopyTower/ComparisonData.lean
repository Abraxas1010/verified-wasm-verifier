import HeytingLean.Algebra.HomotopyTower.LimitEquivalence
import HeytingLean.Algebra.HomotopyTower.GroupoidBridge

namespace HeytingLean
namespace Algebra
namespace HomotopyTower

open CategoryTheory
open HeytingLean.LoF.Combinators.Category

universe u

variable {α : Type u} [Order.Frame α]

/-- Explicit comparison data from the fixed-point tower limit to a transport-groupoid limit.

This now records the strict stagewise tower equivalence data. The actual limit-level comparison
equivalence is derived from `towerLimit_equivalence_of_towerEquivalence`.
-/
structure StableTransportComparison (T : NucleusTower (α := α)) (hfin : FiniteImage T) where
  Q : StableTransportQuiver T hfin
  towerEquiv : TowerEquivalence (fixedPointCatTower T) (stableGroupoidTower Q)

/-- The limit-level comparison equivalence derived from the strict tower comparison data. -/
noncomputable def StableTransportComparison.limitEquiv
    {T : NucleusTower (α := α)} {hfin : FiniteImage T}
    (cmp : StableTransportComparison T hfin) :
    TowerLimit (fixedPointCatTower T) ≌ stableGroupoidLimit cmp.Q :=
  towerLimit_equivalence_of_towerEquivalence cmp.towerEquiv

end HomotopyTower
end Algebra
end HeytingLean
