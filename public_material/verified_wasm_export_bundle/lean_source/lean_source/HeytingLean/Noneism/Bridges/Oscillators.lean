import HeytingLean.Noneism.PrimordialTension
import HeytingLean.Genesis.Iterant
import HeytingLean.Information.Dynamics
import HeytingLean.Information.Primitive
import HeytingLean.Genesis.CoGame
import HeytingLean.Genesis.Stabilization

/-!
# Noneism.Bridges.Oscillators

Phase-1 primordial oscillators.

Note: `Iterant Bool` itself has fixed points under `shift`, so we use the canonical
2-cycle subtype `{phaseI, phaseJ}` as the oscillator carrier.
-/

namespace HeytingLean
namespace Noneism
namespace Bridges

open HeytingLean.Noneism
open HeytingLean.Genesis
open HeytingLean.Information

/-- Canonical two-phase iterant carrier `{phaseI, phaseJ}`. -/
abbrev IterantPhase : Type :=
  { i : Iterant Bool // i = phaseI ∨ i = phaseJ }

namespace IterantPhase

/-- Canonical phase-I element. -/
def phaseIVal : IterantPhase := ⟨phaseI, Or.inl rfl⟩

/-- Canonical phase-J element. -/
def phaseJVal : IterantPhase := ⟨phaseJ, Or.inr rfl⟩

/-- Shift on the canonical two-phase subtype. -/
def step (x : IterantPhase) : IterantPhase :=
  if _hx : x.1 = phaseI then
    phaseJVal
  else
    phaseIVal

/-- Observable bit for the iterant oscillator (`false` at seed). -/
def obs (x : IterantPhase) : Bool := x.1.even

@[simp] theorem step_phaseIVal : step phaseIVal = phaseJVal := by
  simp [step, phaseIVal]

theorem phaseJ_ne_phaseI : phaseJ ≠ phaseI := by
  intro h
  exact phaseI_ne_phaseJ h.symm

@[simp] theorem step_phaseJVal : step phaseJVal = phaseIVal := by
  simp [step, phaseJVal, phaseJ_ne_phaseI]

@[simp] theorem obs_phaseIVal : obs phaseIVal = false := rfl
@[simp] theorem obs_phaseJVal : obs phaseJVal = true := rfl

theorem eq_phaseIVal_or_eq_phaseJVal (x : IterantPhase) : x = phaseIVal ∨ x = phaseJVal := by
  rcases x with ⟨i, hi⟩
  rcases hi with hI | hJ
  · left
    cases hI
    rfl
  · right
    cases hJ
    rfl

@[simp] theorem step_step (x : IterantPhase) : step (step x) = x := by
  rcases eq_phaseIVal_or_eq_phaseJVal x with hI | hJ
  · rw [hI]
    simp
  · rw [hJ]
    simp

@[simp] theorem obs_step (x : IterantPhase) : obs (step x) = Bool.not (obs x) := by
  rcases eq_phaseIVal_or_eq_phaseJVal x with hI | hJ
  · rw [hI]
    rw [step_phaseIVal, obs_phaseJVal, obs_phaseIVal]
    rfl
  · rw [hJ]
    rw [step_phaseJVal, obs_phaseIVal, obs_phaseJVal]
    rfl

end IterantPhase

instance instPrimordialTensionIterantPhase : PrimordialTension IterantPhase where
  engine :=
    { seed := IterantPhase.phaseIVal
      step := IterantPhase.step
      obs := IterantPhase.obs
      step_involutive := by intro x; simp
      obs_flips := by intro x; simp }

namespace InfoStateOsc

/-- Info-state oscillator observable (`false` at the primordial seed). -/
def obs : InfoState → Bool
  | .primordial => false
  | .counter => true

@[simp] theorem obs_primordial : obs .primordial = false := rfl
@[simp] theorem obs_counter : obs .counter = true := rfl

@[simp] theorem obs_step (s : InfoState) : obs (InfoState.step s) = Bool.not (obs s) := by
  cases s <;> rfl

end InfoStateOsc

instance instPrimordialTensionInfoState : PrimordialTension InfoState where
  engine :=
    { seed := .primordial
      step := InfoState.step
      obs := InfoStateOsc.obs
      step_involutive := by intro s; simp
      obs_flips := by intro s; simp }

namespace SideOsc

/-- Side oscillator step (inside/outside toggle). -/
def step : Side → Side
  | .inside => .outside
  | .outside => .inside

/-- Side oscillator observable (`false` at the inside seed). -/
def obs : Side → Bool
  | .inside => false
  | .outside => true

@[simp] theorem step_inside : step .inside = .outside := rfl
@[simp] theorem step_outside : step .outside = .inside := rfl

@[simp] theorem obs_inside : obs .inside = false := rfl
@[simp] theorem obs_outside : obs .outside = true := rfl

@[simp] theorem step_step (s : Side) : step (step s) = s := by
  cases s <;> rfl

@[simp] theorem obs_step (s : Side) : obs (step s) = Bool.not (obs s) := by
  cases s <;> rfl

end SideOsc

instance instPrimordialTensionSide : PrimordialTension Side where
  engine :=
    { seed := .inside
      step := SideOsc.step
      obs := SideOsc.obs
      step_involutive := by intro s; simp
      obs_flips := by intro s; simp }

/-- Genesis game polarity: Void (no options) vs Life (self-referential). -/
inductive GamePolarity where
  | void
  | life
  deriving Repr, DecidableEq

namespace GamePolarity

def step : GamePolarity → GamePolarity
  | .void => .life
  | .life => .void

def obs : GamePolarity → Bool
  | .void => false
  | .life => true

@[simp] theorem step_step (p : GamePolarity) : step (step p) = p := by
  cases p <;> rfl

@[simp] theorem obs_step (p : GamePolarity) : obs (step p) = Bool.not (obs p) := by
  cases p <;> rfl

/-- Map game polarity states to the corresponding genesis co-game. -/
def toCoGame : GamePolarity → Genesis.CoGame
  | .void => Genesis.CoGame.Void
  | .life => Genesis.CoGame.Life

@[simp] theorem toCoGame_void : toCoGame .void = Genesis.CoGame.Void := rfl
@[simp] theorem toCoGame_life : toCoGame .life = Genesis.CoGame.Life := rfl

/-- Stabilization oscillation expression induced by game polarity. -/
theorem oscillationExpr_of_polarity (p : GamePolarity) :
    Genesis.oscillationExpr (toCoGame p) =
      match p with
      | .void => HeytingLean.LoF.LoFSecond.Expr.void
      | .life => HeytingLean.LoF.LoFSecond.Expr.reentry := by
  cases p <;> simp [toCoGame]

end GamePolarity

instance instPrimordialTensionGamePolarity : PrimordialTension GamePolarity where
  engine :=
    { seed := .void
      step := GamePolarity.step
      obs := GamePolarity.obs
      step_involutive := by intro p; simp
      obs_flips := by intro p; simp }

/-- The 0-sphere with antipodal involution. -/
inductive ZeroSphere where
  | north
  | south
  deriving Repr, DecidableEq

namespace ZeroSphere

def step : ZeroSphere → ZeroSphere
  | .north => .south
  | .south => .north

def obs : ZeroSphere → Bool
  | .north => false
  | .south => true

@[simp] theorem step_step (z : ZeroSphere) : step (step z) = z := by
  cases z <;> rfl

@[simp] theorem obs_step (z : ZeroSphere) : obs (step z) = Bool.not (obs z) := by
  cases z <;> rfl

end ZeroSphere

instance instPrimordialTensionZeroSphere : PrimordialTension ZeroSphere where
  engine :=
    { seed := .north
      step := ZeroSphere.step
      obs := ZeroSphere.obs
      step_involutive := by intro z; simp
      obs_flips := by intro z; simp }

/-- Conway star-player polarity as a two-cycle carrier. -/
inductive StarPlayer where
  | left
  | right
  deriving Repr, DecidableEq

namespace StarPlayer

def step : StarPlayer → StarPlayer
  | .left => .right
  | .right => .left

def obs : StarPlayer → Bool
  | .left => false
  | .right => true

@[simp] theorem step_step (p : StarPlayer) : step (step p) = p := by
  cases p <;> rfl

@[simp] theorem obs_step (p : StarPlayer) : obs (step p) = Bool.not (obs p) := by
  cases p <;> rfl

end StarPlayer

instance instPrimordialTensionStarPlayer : PrimordialTension StarPlayer where
  engine :=
    { seed := .left
      step := StarPlayer.step
      obs := StarPlayer.obs
      step_involutive := by intro p; simp
      obs_flips := by intro p; simp }

end Bridges
end Noneism
end HeytingLean
