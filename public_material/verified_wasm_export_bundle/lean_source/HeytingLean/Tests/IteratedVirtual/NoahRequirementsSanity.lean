import HeytingLean.IteratedVirtual.KCellCobordism
import HeytingLean.IteratedVirtual.SpiralCobordism
import HeytingLean.IteratedVirtual.StrictOmega
import HeytingLean.IteratedVirtual.SpiralEnergy

/-!
# Tests.IteratedVirtual.NoahRequirementsSanity

Compile-only sanity checks that the “Noah requirements” interfaces exist:
- k-cells as globe-maps,
- cobordisms and virtual compositions between k-cells (as morphisms in `GlobularSet`),
- a `k → ∞` (atTop) tension-minimization statement for the helix energy functional.
-/

namespace HeytingLean
namespace Tests
namespace IteratedVirtual

open HeytingLean.IteratedVirtual

-- `GlobularSet` is a category; k-cells are morphisms.
#check (inferInstance : CategoryTheory.Category HeytingLean.IteratedVirtual.GlobularSet)
#check HeytingLean.IteratedVirtual.kCell
#check HeytingLean.IteratedVirtual.KCellCobordism
#check HeytingLean.IteratedVirtual.KCellVirtualCobordism

-- Trivial “Catₙ” example exists and has a 22-cell.
def terminal_cell22' :
    HeytingLean.IteratedVirtual.StrictNCat.Cell22 (HeytingLean.IteratedVirtual.Examples.terminalNCat 22) :=
  { map := fun _ _ => PUnit.unit
    map_src := by intro n x; rfl
    map_tgt := by intro n x; rfl }

-- A cobordism between parallel k-cells (here: the same k-cell).
def terminal_kcell (k : Nat) :
    HeytingLean.IteratedVirtual.kCell (X := HeytingLean.IteratedVirtual.Examples.terminalGlobularSet) k :=
  { map := fun _ _ => PUnit.unit
    map_src := by intro n x; rfl
    map_tgt := by intro n x; rfl }

def terminal_kcell_cobordism (k : Nat) :
    HeytingLean.IteratedVirtual.KCellCobordism
      (X := HeytingLean.IteratedVirtual.Examples.terminalGlobularSet) k (terminal_kcell k) (terminal_kcell k) :=
  HeytingLean.IteratedVirtual.CobordismHom.refl (C := HeytingLean.IteratedVirtual.GlobularSet) (terminal_kcell k)

-- Virtual composition: trivial chain.
def terminal_kcell_virtual (k : Nat) :
    HeytingLean.IteratedVirtual.KCellVirtualCobordism
      (X := HeytingLean.IteratedVirtual.Examples.terminalGlobularSet) k (terminal_kcell k) (terminal_kcell k) :=
  HeytingLean.IteratedVirtual.VirtualCobordismHom.refl (C := HeytingLean.IteratedVirtual.GlobularSet) (terminal_kcell k)

-- “k → ∞” (atTop) helix energy tends to 0.
example (pitch : ℝ) :
    Filter.Tendsto
      (fun k : Nat =>
        HeytingLean.IteratedVirtual.Point3R.tensionEnergyAt (t := (k : ℝ)) pitch
          (HeytingLean.IteratedVirtual.Point3R.helix (t := (k : ℝ)) pitch))
      Filter.atTop (nhds (0 : ℝ)) :=
  HeytingLean.IteratedVirtual.Point3R.tendsto_tensionEnergyAt_helix_atTop pitch

end IteratedVirtual
end Tests
end HeytingLean
