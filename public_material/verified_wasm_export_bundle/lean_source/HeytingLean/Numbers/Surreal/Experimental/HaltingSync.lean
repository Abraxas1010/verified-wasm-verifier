import HeytingLean.Numbers.Surreal.Experimental.KinematicForcing

namespace HeytingLean
namespace Numbers
namespace Surreal
namespace Experimental

/-- Classification outcomes for actual/counterfactual synchronization. -/
inductive SyncOutcome where
  | halt
  | horizon
  | running
  deriving Repr, DecidableEq

/-- Minimal process state with actual and counterfactual branches. -/
structure SyncProcess where
  fuel : Nat
  actual : KinematicWorld
  counterfactual : KinematicWorld
  deriving Repr, DecidableEq

/-- Process halts when fuel reaches zero. -/
def halts (p : SyncProcess) : Prop := p.fuel = 0

/-- Process is horizon-blocked if either branch exceeds budget. -/
def horizonBlocked (budget : Nat) (p : SyncProcess) : Bool :=
  decide (horizon budget p.actual) || decide (horizon budget p.counterfactual)

/-- Classifier used by the synchronization lane. -/
def classify (budget : Nat) (p : SyncProcess) : SyncOutcome :=
  if p.fuel = 0 then .halt else if horizonBlocked budget p then .horizon else .running

@[simp] theorem classify_of_halts {budget : Nat} {p : SyncProcess}
    (h : halts p) :
    classify budget p = .halt := by
  unfold halts at h
  simp [classify, h]

@[simp] theorem classify_of_horizon {budget : Nat} {p : SyncProcess}
    (hNotHalt : ¬ halts p) (hH : horizonBlocked budget p = true) :
    classify budget p = .horizon := by
  have hFuelNe : p.fuel ≠ 0 := by
    simpa [halts] using hNotHalt
  simp [classify, hFuelNe, hH]

@[simp] theorem classify_running_of_not_halt_not_horizon
    {budget : Nat} {p : SyncProcess}
    (hNotHalt : ¬ halts p) (hNotH : horizonBlocked budget p = false) :
    classify budget p = .running := by
  have hFuelNe : p.fuel ≠ 0 := by
    simpa [halts] using hNotHalt
  simp [classify, hFuelNe, hNotH]

/-- Toy recursive process used for executable halt/horizon classification checks. -/
def toyProcess (fuel velocity : Nat) : SyncProcess :=
  { fuel := fuel
    actual := { stage := 0, velocity := velocity }
    counterfactual := { stage := 1, velocity := velocity } }

theorem toyProcess_halts_classification (budget velocity : Nat) :
    classify budget (toyProcess 0 velocity) = .halt := by
  simp [classify, toyProcess]

theorem toyProcess_horizon_classification {budget fuel velocity : Nat}
    (hFuel : fuel ≠ 0) (hVel : budget < velocity) :
    classify budget (toyProcess fuel velocity) = .horizon := by
  have hNotHalt : ¬ halts (toyProcess fuel velocity) := by
    simpa [halts, toyProcess] using hFuel
  have hHorizon : horizonBlocked budget (toyProcess fuel velocity) = true := by
    have hLeft : decide (horizon budget (toyProcess fuel velocity).actual) = true := by
      exact decide_eq_true (by simpa [horizon, toyProcess] using hVel)
    simp [horizonBlocked, hLeft]
  exact classify_of_horizon hNotHalt hHorizon

end Experimental
end Surreal
end Numbers
end HeytingLean
