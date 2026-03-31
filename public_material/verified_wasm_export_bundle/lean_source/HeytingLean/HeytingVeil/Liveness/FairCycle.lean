import HeytingLean.HeytingVeil.Liveness.Core

namespace HeytingLean
namespace HeytingVeil
namespace Liveness

open HeytingLean.HeytingVeil.ModelCheck

universe u

structure FairCycleWitness (State : Type u) where
  repeated : State
  path : List State
  fairness : String
  deriving Repr

private def deterministicNext? {State : Type u} [DecidableEq State]
    (dm : DecidableMachine State) (s : State) : Option State :=
  (successors dm s).head?

private def walkFrom {State : Type u} [DecidableEq State]
    (dm : DecidableMachine State) : Nat → State → List State
  | 0, s => [s]
  | k + 1, s =>
      match deterministicNext? dm s with
      | none => [s]
      | some t => s :: walkFrom dm k t

private def firstRepeat? {State : Type u} [DecidableEq State] : List State → List State → Option State
  | [], _ => none
  | s :: rest, seen =>
      if s ∈ seen then some s else firstRepeat? rest (s :: seen)

def fairCycleCheck {State : Type u} [DecidableEq State]
    (dm : DecidableMachine State) (k : Nat) (fairness : String := "weak") :
    Option (FairCycleWitness State) :=
  match (initStates dm).head? with
  | none => none
  | some s0 =>
      let path := walkFrom dm k s0
      match firstRepeat? path [] with
      | none => none
      | some rep =>
          some { repeated := rep, path := path, fairness := fairness }

end Liveness
end HeytingVeil
end HeytingLean
