import HeytingLean.Cybernetics.Observer
import HeytingLean.Cybernetics.Feedback
import HeytingLean.Cybernetics.Measured
import HeytingLean.Cybernetics.Trajectory

namespace HeytingLean
namespace CLI

open HeytingLean.Cybernetics

def SOCDemo.run : IO Unit := do
  let O : Observer Bool Nat := { observe := fun n => n % 2 = 0 }
  let F : Feedback Nat Bool := { step := fun s o => if o then s + 1 else s + 2 }
  let MO : MeasuredObserver Bool Nat Float :=
    MeasuredObserver.fromObserver O (fun a b => if a = b then 0.0 else 1.0)
  let (states, errs) := Cybernetics.Run.iterateMeasured MO F 0 12
  let embedNat (n : Nat) : Metrics.FlowPoint := #[Float.ofNat n, 0.0]
  let summ := Cybernetics.Trajectory.summarize embedNat states
  IO.println s!"SOC demo — steps: {summ.count} perimeter: {summ.perimeter} area: {summ.area}"
  IO.println s!"avgSpeed: {summ.avgSpeed} avgCurv: {summ.avgCurv}"
  IO.println s!"errors: {errs}"

end CLI
end HeytingLean

def main : IO Unit :=
  HeytingLean.CLI.SOCDemo.run

