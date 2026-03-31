import HeytingLean.Constructor.Crypto.ImpossibleTasks
import HeytingLean.Constructor.CT.InformationSound

/-!
# No-cloning as a CT impossibility predicate (constructor-existence layer)

This file provides a small vocabulary layer around the common “no-cloning” premise used in
constructor-theoretic security reductions.
-/

namespace HeytingLean
namespace Constructor
namespace Crypto

open HeytingLean.Constructor.CT

universe u

variable {σ : Type u}

/-- A no-cloning premise for a designated cloning task. -/
def NoCloning (CT : TaskCT σ) (Tclone : CloningTask σ) : Prop :=
  CT.impossible Tclone.task

/-- A reusable wrapper: a superinformation medium provides a canonical no-cloning premise. -/
theorem noCloning_of_superinformation {CT : TaskCT σ} (M : TaskCT.SuperinformationMedium σ CT) :
    NoCloning CT ⟨M.copyXY⟩ :=
  M.no_copyXY

end Crypto
end Constructor
end HeytingLean

