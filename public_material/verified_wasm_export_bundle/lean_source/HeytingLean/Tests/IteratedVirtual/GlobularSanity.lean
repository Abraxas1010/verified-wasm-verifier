import HeytingLean.IteratedVirtual.StrictOmega
import HeytingLean.IteratedVirtual.SpiralEnergy

/-!
# Tests.IteratedVirtual.GlobularSanity

Compile-only sanity checks for:
- globular sets + walking globes,
- the minimal strict ω-category wrapper,
- the discrete “tension energy” theorem.
-/

namespace HeytingLean
namespace Tests
namespace IteratedVirtual

open HeytingLean.IteratedVirtual

-- A walking globe exists for any k.
#check HeytingLean.IteratedVirtual.Globe
#check HeytingLean.IteratedVirtual.kCell

-- The terminal strict n-category has a canonical 22-cell (unique globe-map into PUnit levels).
def terminal_cell22 : HeytingLean.IteratedVirtual.StrictNCat.Cell22 (HeytingLean.IteratedVirtual.Examples.terminalNCat 22) :=
  { map := fun _ _ => PUnit.unit
    map_src := by
      intro n x
      rfl
    map_tgt := by
      intro n x
      rfl }

-- The “tension” functional is nonnegative, and the helix minimizes it pointwise.
example (t pitch : ℝ) (p : HeytingLean.IteratedVirtual.Point3R) :
    HeytingLean.IteratedVirtual.Point3R.tensionEnergyAt t pitch (HeytingLean.IteratedVirtual.Point3R.helix t pitch) ≤
      HeytingLean.IteratedVirtual.Point3R.tensionEnergyAt t pitch p :=
  HeytingLean.IteratedVirtual.Point3R.helix_minimizes_pointwise t pitch p

end IteratedVirtual
end Tests
end HeytingLean
