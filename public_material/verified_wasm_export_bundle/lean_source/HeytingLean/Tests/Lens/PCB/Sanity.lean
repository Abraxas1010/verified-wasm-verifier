import HeytingLean.Lens.PCB.Single
import HeytingLean.Lens.PCB.Multi
import HeytingLean.Lens.PCB.ReentryInstances
import HeytingLean.LoF.Nucleus

/-! Compile-only sanity for PCB lenses. -/

namespace HeytingLean
namespace Tests
namespace Lens
namespace PCB

open HeytingLean.Lens.PCB

-- Take Ω = String for demonstration
instance : Inhabited String := ⟨""⟩
instance : DecidableEq String := inferInstance

def idPolicy : SingleUpdatePolicy String :=
  { put := fun _ b => b
  , put_get_id := by intro h; rfl
  , view_consistency := by intro h b'; rfl }

def mid : SingleState String := SingleState.fromHi (Ω := String) "hello"

def mid' : SingleState String := SingleState.update idPolicy mid "world"

-- Multi variant needs a trivial lifter consistent with mapCoalesce
noncomputable def idLift : MultiUpdatePolicy String :=
  { lift := fun d => d }

noncomputable def ms0 : MultiState String := MultiState.fromHiDist (Ω := String) (HeytingLean.Probability.Dist.fromPairs #[("a",1),("b",1)])

noncomputable def ms1 : MultiState String := MultiState.update idLift ms0 (HeytingLean.Probability.Dist.fromPairs #[("x",2),("y",1)])

/-- Under the identity policy, a single-state update replaces the high-level
value by the Booleanized input. -/
example : mid'.hi = "world" := rfl

-- Reentry Ω demo (compile-only): Ω := R.Omega
section
open HeytingLean.LoF
variable [HeytingLean.LoF.PrimaryAlgebra α]
variable (R : Reentry α)

def sΩ : HeytingLean.Lens.PCB.SingleState (R.Omega) :=
  HeytingLean.Lens.PCB.SingleState.fromHi (R.process)

def sΩ' : HeytingLean.Lens.PCB.SingleState (R.Omega) :=
  let s := sΩ (R := R)
  HeytingLean.Lens.PCB.SingleState.update (HeytingLean.Lens.PCB.singleIdPolicy R) s (R.counterProcess)

end

end PCB
end Lens
end Tests
end HeytingLean
