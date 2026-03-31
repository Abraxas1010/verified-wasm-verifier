import HeytingLean.OTM.Tape

namespace HeytingLean
namespace OTM

universe u v

/-- Transition payload emitted by one OTM control step. -/
structure TransitionPacket (α : Type v) where
  nextState : α
  move : HeadMove
  writeVal : α
  deriving Repr

/-- Runtime control snapshot for an OTM instance. -/
structure OTMState (ι : Type u) (α : Type v) where
  head : ι
  control : α
  deriving Repr

/--
Phase-A OTM assembly:
- nucleus/re-entry/ratchet wrappers from existing subsystems,
- index-parametric fixed-point tape,
- transition and head-advance kernels.
-/
structure Machine (ι : Type u) (α : Type v) [DecidableEq ι] [LoF.PrimaryAlgebra α] where
  nucleus : NucleusInterface α
  reentry : ReentryInterface α
  ratchet : RatchetInterface α
  nucleus_reentry_compat : ∀ x : α, reentry.core.nucleus x = nucleus.core.R x
  tape : Tape ι α nucleus.core
  runtime : OTMState ι α
  advanceHead : ι → HeadMove → ι
  transition : α → α → TransitionPacket α
  transition_fixed :
    ∀ σ c, nucleus.core.R (transition σ c).writeVal = (transition σ c).writeVal

namespace Machine

variable {ι : Type u} {α : Type v} [DecidableEq ι] [LoF.PrimaryAlgebra α]

/-- Read the cell under the current head. -/
def readCurrent (M : Machine ι α) : α :=
  M.tape.read M.runtime.head

/-- Execute one deterministic OTM step. -/
def step (M : Machine ι α) : Machine ι α :=
  let cell := M.readCurrent
  let out := M.transition M.runtime.control cell
  let tape' := M.tape.write M.runtime.head out.writeVal (M.transition_fixed _ _)
  { M with
      tape := tape'
      runtime :=
        { head := M.advanceHead M.runtime.head out.move
          control := out.nextState } }

/-- Fuel-bounded deterministic OTM execution. -/
def run : Nat → Machine ι α → Machine ι α
  | 0, M => M
  | Nat.succ n, M => run n (M.step)

@[simp] theorem run_zero (M : Machine ι α) : run 0 M = M := rfl

@[simp] theorem run_succ (n : Nat) (M : Machine ι α) :
    run (Nat.succ n) M = run n (M.step) := rfl

@[simp] theorem step_read_old_head (M : Machine ι α) :
    (M.step).tape.read M.runtime.head
      = (M.transition M.runtime.control M.readCurrent).writeVal := by
  simp [step, readCurrent]

theorem step_tape_fixed (M : Machine ι α) (i : ι) :
    M.nucleus.core.R ((M.step).tape.read i) = (M.step).tape.read i := by
  exact (M.step).tape.fixed i

end Machine

end OTM
end HeytingLean
