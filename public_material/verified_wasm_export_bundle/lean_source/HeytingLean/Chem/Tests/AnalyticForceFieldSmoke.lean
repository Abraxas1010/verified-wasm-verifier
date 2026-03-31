import HeytingLean.Chem.Interactions.Analytic.ForceField
import HeytingLean.Chem.PeriodicTable.Elements

/-!
# Analytic force-field smoke test

Compile-only: confirms the Real/`sqrt`/`exp` layer imports and basic definitions reduce.
-/

namespace HeytingLean
namespace Chem
namespace Tests

open HeytingLean.Chem
open HeytingLean.Chem.Interactions.Analytic
open HeytingLean.Chem.PeriodicTable.Elements

noncomputable section

example : True := by
  let ff : ForceField := { pair := lennardJones { epsilon := 1, sigma := 1 } }
  let cfg : Configuration 1 :=
    { atoms := fun _ => { element := H, charge := 0 }
      pos := fun _ => fun _ => 0 }
  -- With 1 atom there are no pairs, so the total pair energy is 0.
  have hEmpty : pairIndexSet 1 = (∅ : Finset (Fin 1 × Fin 1)) := by
    ext p
    constructor
    · intro hp
      -- In `Fin 1`, any two indices are equal, so `p.1 < p.2` is impossible.
      unfold pairIndexSet at hp
      have hp_lt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
      have hEq : p.1 = p.2 := by
        simpa using (Subsingleton.elim p.1 p.2)
      have hNot : ¬ p.1 < p.2 := by
        simp [hEq]
      exact (hNot hp_lt).elim
    · intro hp
      cases hp
  have : totalPairEnergy ff cfg = 0 := by
    simp [totalPairEnergy, hEmpty]
  trivial

end
end Tests
end Chem
end HeytingLean
