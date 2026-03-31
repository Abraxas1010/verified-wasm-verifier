import HeytingLean.Chem.QED.BoundState.Hamiltonian
import HeytingLean.Chem.QED.BoundState.RadiativePotentials

/-!
# Bound-state model smoke tests
-/

namespace HeytingLean
namespace Chem
namespace Tests

open HeytingLean.Chem.QED.BoundState

example : uehling.tag = RadiativeCorrection.vacuumPolarization := by
  rfl

-- Compile-only: construct an effective model over `ℤ` on a trivial 1D state space.
example : True := by
  let S : Type := ℤ
  -- A degenerate Hamiltonian (zero operator), as a placeholder.
  let H0 : Hamiltonian ℤ S := { H := 0 }
  let base : BaseModel ℤ S := { name := "toy", ham := H0 }
  let eff : EffectiveModel ℤ S := { base := base, corrections := [uehling] }
  -- `op` is defined and reduces to the base operator at this stage.
  have : eff.op = base.op := by
    rfl
  trivial

end Tests
end Chem
end HeytingLean
