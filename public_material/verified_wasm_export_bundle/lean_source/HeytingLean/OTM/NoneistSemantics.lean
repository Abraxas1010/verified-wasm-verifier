import HeytingLean.OTM.Assembly

namespace HeytingLean
namespace OTM

universe u v

variable {ι : Type u} {α : Type v}
variable [DecidableEq ι] [LoF.PrimaryAlgebra α]

/-- Lens-relative noneist existence tag carried by OTM runtime states. -/
inductive ExistenceMode where
  | manifest
  | withdrawn
  deriving DecidableEq, Repr

/-- Runtime shadow payload induced by an existence mode. -/
def shadowOf (mode : ExistenceMode) (control : α) : Option α :=
  match mode with
  | .manifest => some control
  | .withdrawn => none

/-- OTM machine state enriched with a noneist existence tag and shadow payload. -/
structure NoneistState (ι : Type u) (α : Type v) [DecidableEq ι] [LoF.PrimaryAlgebra α] where
  machine : Machine ι α
  mode : ExistenceMode
  shadow : Option α

namespace NoneistState

/-- Well-typed noneist state: shadow payload must match existence mode and machine control. -/
def WellTyped (S : NoneistState ι α) : Prop :=
  S.shadow = shadowOf S.mode S.machine.runtime.control

/-- Canonical constructor from an OTM machine and existence mode. -/
def ofMachine (M : Machine ι α) (mode : ExistenceMode) : NoneistState ι α :=
  { machine := M
    mode := mode
    shadow := shadowOf mode M.runtime.control }

@[simp] theorem wellTyped_ofMachine (M : Machine ι α) (mode : ExistenceMode) :
    (ofMachine (ι := ι) (α := α) M mode).WellTyped := by
  simp [WellTyped, ofMachine]

end NoneistState

/-- Public predicate name for Phase-D noneist state typing. -/
def otm_state_welltyped (S : NoneistState ι α) : Prop :=
  S.WellTyped

/-- One noneist-aware OTM transition step (tag-preserving, shadow-recomputed). -/
def noneistStep (S : NoneistState ι α) : NoneistState ι α :=
  NoneistState.ofMachine (ι := ι) (α := α) S.machine.step S.mode

/-- Fuel-bounded noneist-aware OTM execution. -/
def noneistRun : Nat → NoneistState ι α → NoneistState ι α
  | 0, S => S
  | Nat.succ fuel, S => noneistRun fuel (noneistStep S)

@[simp] theorem noneistRun_zero (S : NoneistState ι α) :
    noneistRun 0 S = S := rfl

@[simp] theorem noneistRun_succ (fuel : Nat) (S : NoneistState ι α) :
    noneistRun (Nat.succ fuel) S = noneistRun fuel (noneistStep S) := rfl

/-- Phase-D core theorem: noneist typing is preserved by one OTM transition. -/
theorem otm_transition_preserves_noneist_wellformedness
    (S : NoneistState ι α) (_hS : otm_state_welltyped S) :
    otm_state_welltyped (noneistStep S) := by
  simp [otm_state_welltyped, noneistStep, NoneistState.WellTyped, NoneistState.ofMachine]

/-- Phase-D trace theorem: noneist typing is preserved along fuel-bounded runs. -/
theorem noneistRun_preserves_welltyped :
    ∀ (fuel : Nat) (S : NoneistState ι α),
      otm_state_welltyped S → otm_state_welltyped (noneistRun fuel S)
  | 0, _, hS => hS
  | Nat.succ fuel, S, hS =>
      noneistRun_preserves_welltyped fuel (noneistStep S)
        (otm_transition_preserves_noneist_wellformedness S hS)

/-- Default noneist tagging of a machine state. -/
def initialNoneistState (M : Machine ι α) (mode : ExistenceMode := .manifest) : NoneistState ι α :=
  NoneistState.ofMachine (ι := ι) (α := α) M mode

@[simp] theorem initialNoneistState_welltyped (M : Machine ι α) (mode : ExistenceMode := .manifest) :
    otm_state_welltyped (initialNoneistState M mode) := by
  simp [initialNoneistState, otm_state_welltyped]

/-- Machine projection: noneist run tracks ordinary machine run exactly. -/
theorem noneistRun_machine_eq_machine_run
    (mode : ExistenceMode := .manifest) :
    ∀ fuel (M : Machine ι α),
      (noneistRun fuel (initialNoneistState M mode)).machine = Machine.run fuel M
  | 0, M => rfl
  | Nat.succ fuel, M => by
      simpa [noneistRun, initialNoneistState, noneistStep, Machine.run]
        using noneistRun_machine_eq_machine_run (mode := mode) fuel M.step

/--
Phase-D witness theorem:
an initialized noneist-tagged OTM state remains well-typed along runs, and the
projected machine trace is exactly the ordinary OTM run trace.
-/
theorem otm_noneist_states_witness (M : Machine ι α) (mode : ExistenceMode := .manifest) :
    ∀ fuel,
      otm_state_welltyped (noneistRun fuel (initialNoneistState M mode)) ∧
      (noneistRun fuel (initialNoneistState M mode)).machine = Machine.run fuel M := by
  intro fuel
  exact ⟨
    noneistRun_preserves_welltyped fuel (initialNoneistState M mode)
      (initialNoneistState_welltyped M mode),
    noneistRun_machine_eq_machine_run (mode := mode) fuel M
  ⟩

end OTM
end HeytingLean
