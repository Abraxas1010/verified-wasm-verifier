import HeytingLean.Cybernetics.Observer
import HeytingLean.Cybernetics.Feedback

/-
Second-Order Cybernetics: Measured observers and measured closed-loop runs.
-/

namespace HeytingLean
namespace Cybernetics

universe u

structure MeasuredObserver (Obs : Type u) (Sys : Type u) (Err : Type u) where
  measure : Sys → Obs
  error   : Obs → Obs → Err

namespace MeasuredObserver
variable {Obs Sys Err : Type u}

@[simp] def fromObserver (O : Observer Obs Sys) (err : Obs → Obs → Err) :
    MeasuredObserver Obs Sys Err :=
  { measure := O.observe, error := err }

end MeasuredObserver

namespace Run
variable {Sys Obs Err : Type u}

@[simp] def stepMeasured
    (O : MeasuredObserver Obs Sys Err)
    (F : Feedback Sys Obs)
    (s : Sys) : Sys × Err :=
  let o₀ := O.measure s
  let s' := F.step s o₀
  let o₁ := O.measure s'
  (s', O.error o₁ o₀)

@[simp] def iterateMeasured
    (O : MeasuredObserver Obs Sys Err)
    (F : Feedback Sys Obs) (s0 : Sys) (steps : Nat)
    : Array Sys × Array Err :=
  Id.run do
    let mut states : Array Sys := Array.mkEmpty (steps+1)
    let mut errs   : Array Err := Array.mkEmpty steps
    let mut s := s0
    states := states.push s
    for _i in [:steps] do
      let (s', e) := stepMeasured O F s
      s := s'
      states := states.push s
      errs := errs.push e
    return (states, errs)

end Run

end Cybernetics
end HeytingLean

