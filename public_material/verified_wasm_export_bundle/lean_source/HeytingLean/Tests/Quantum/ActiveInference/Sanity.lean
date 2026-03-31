import HeytingLean.Quantum.ActiveInference.Core

/-
Compile-only sanity for discrete active inference.
-/

namespace HeytingLean
namespace Tests
namespace Quantum
namespace ActiveInference

open HeytingLean.Quantum.ActiveInference

def model : DiscreteModel :=
  let prior : Array Float := #[0.5, 0.5]
  let likeA0 : Array (Array Float) := #[#[0.8, 0.2], #[0.2, 0.8]]
  let likeA1 : Array (Array Float) := #[#[0.5, 0.5], #[0.5, 0.5]]
  { ns := 2, no := 2, na := 2, prior := prior, like := #[likeA0, likeA1] }

def pref : Preferences := { prefObs? := some #[0.7, 0.3] }

def post : Array Float := posterior model 0 0
def f    : Float := freeEnergy model 0 0
def eA0  : Float := efe model pref 0
def eA1  : Float := efe model pref 1
def best : Nat := bestAction model pref

end ActiveInference
end Quantum
end Tests
end HeytingLean

