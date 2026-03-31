import HeytingLean.Cybernetics.Observer
import HeytingLean.Cybernetics.Feedback
import HeytingLean.Metrics.Curvature

/-
Second-Order Cybernetics: Trajectory iteration and simple geometric summaries
using the existing Flow metrics (finite differences, perimeter, area).
-/

namespace HeytingLean
namespace Cybernetics

open HeytingLean.Metrics

universe u

namespace Trajectory
variable {Sys Obs : Type u}

@[simp] def iterate (O : Observer Obs Sys) (F : Feedback Sys Obs)
    (s0 : Sys) (steps : Nat) : Array Sys :=
  Id.run do
    let mut states : Array Sys := Array.mkEmpty (steps+1)
    let mut s := s0
    states := states.push s
    for _i in [:steps] do
      s := Feedback.loop O F s
      states := states.push s
    return states

structure Summary where
  count     : Nat
  perimeter : Float
  area      : Float
  avgSpeed  : Float
  avgCurv   : Float
deriving Repr

@[simp] def summarize
    (embed : Sys → FlowPoint)
    (states : Array Sys) : Summary :=
  let traj := states.map embed
  let vels := finiteDiff traj
  let speed : Float := Id.run do
    let mut s : Float := 0.0
    for i in [:vels.size] do
      s := s + l2Dist #[] vels[i]!
    if vels.size = 0 then
      return 0.0
    else
      return s / (Float.ofNat vels.size)
  let curv : Float := Id.run do
    let mut s : Float := 0.0
    let n := traj.size
    if n < 3 then return 0.0
    for i in [:n-2] do
      s := s + mengerCurvature (traj[i]!) (traj[i+1]!) (traj[i+2]!)
    return s / (Float.ofNat (n-2))
  { count := states.size
    , perimeter := perimeter2D traj
    , area := area2D traj
    , avgSpeed := speed
    , avgCurv := curv }

end Trajectory

end Cybernetics
end HeytingLean
