import HeytingLean.LoF.Nucleus
import HeytingLean.Lens.PCB.Single
import HeytingLean.Lens.PCB.Multi

/-!
Concrete PCB lens policies instantiated for Ω = R.Omega (fixed points of a Reentry nucleus).
- Single-state identity policy (Boolean view is the same carrier via Reg shim).
- Multi-branch identity lift (under Reg=Ω definalias and canonicalization cleanup).
-/

namespace HeytingLean
namespace Lens
namespace PCB

open HeytingLean.LoF
open HeytingLean.Logic
open HeytingLean.Probability
open scoped Classical

universe u

variable {α : Type u} [PrimaryAlgebra α]

def singleIdPolicy (R : Reentry α) : SingleUpdatePolicy (R.Omega) :=
  { put := fun _ b => b
  , put_get_id := by intro h; rfl
  , view_consistency := by intro h b'; rfl }

noncomputable instance instInhabitedOmega (R : Reentry α) : Inhabited (R.Omega) := ⟨R.process⟩
noncomputable instance instDecEqOmega (R : Reentry α) : DecidableEq (R.Omega) := Classical.decEq _

noncomputable def multiIdLift (R : Reentry α) : MultiUpdatePolicy (R.Omega) :=
  PCB.liftFrom (Ω := R.Omega) (lift := id)

end PCB
end Lens
end HeytingLean
