import HeytingLean.HeytingVeil.ModelCheck.BFS

namespace HeytingLean
namespace HeytingVeil
namespace Liveness

open HeytingLean.HeytingVeil.Temporal
open HeytingLean.HeytingVeil.ModelCheck

universe u

def LivenessProperty {State : Type u} (M : Machine State) (P : State → Prop) : Prop :=
  ∀ σ : Trace State, ValidTrace M σ → Eventually (fun n => P (σ n))

def allPathsHitWithin {State : Type u} [DecidableEq State]
    (dm : DecidableMachine State) (P : State → Prop) [DecidablePred P] : Nat → State → Bool
  | 0, s => decide (P s)
  | k + 1, s =>
      if decide (P s) then
        true
      else
        let succs := successors dm s
        if succs.isEmpty then false else succs.all (fun t => allPathsHitWithin dm P k t)

def kLivenessCheck {State : Type u} [DecidableEq State]
    (dm : DecidableMachine State) (P : State → Prop) [DecidablePred P] (k : Nat) : Bool :=
  (initStates dm).all (fun s => allPathsHitWithin dm P k s)

theorem kLivenessCheck_sound {State : Type u} [DecidableEq State]
    (dm : DecidableMachine State) (P : State → Prop) [DecidablePred P] (k : Nat)
    (h : kLivenessCheck dm P k = true) :
    ∀ s, s ∈ initStates dm → allPathsHitWithin dm P k s = true := by
  intro s hs
  unfold kLivenessCheck at h
  exact List.all_eq_true.mp h s hs

end Liveness
end HeytingVeil
end HeytingLean
