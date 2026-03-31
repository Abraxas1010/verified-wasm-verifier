import HeytingLean.Cybernetics.Observer
import HeytingLean.Cybernetics.Feedback
import HeytingLean.Cybernetics.Trajectory

/-
Compile-only: build a Nat trajectory and summarize with Flow metrics.
-/

namespace HeytingLean
namespace Tests
namespace Cybernetics

open HeytingLean.Cybernetics

def Oparity : Observer Bool Nat := { observe := fun n => n % 2 = 0 }
def Fincr : Feedback Nat Bool := { step := fun s o => if o then s + 1 else s + 2 }

def states : Array Nat := Trajectory.iterate Oparity Fincr 0 10

def embedNat (n : Nat) : Metrics.FlowPoint := #[Float.ofNat n, 0.0]
def summary : Trajectory.Summary := Trajectory.summarize embedNat states

end Cybernetics
end Tests
end HeytingLean

