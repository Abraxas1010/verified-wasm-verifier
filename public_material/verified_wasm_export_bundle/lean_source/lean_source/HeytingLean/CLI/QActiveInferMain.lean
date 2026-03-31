import HeytingLean.Quantum.ActiveInference.Core

namespace HeytingLean
namespace CLI

open HeytingLean.Quantum.ActiveInference

def QActiveInfer.run : IO Unit := do
  -- Small 2-state, 2-observation, 2-action model
  let prior : Array Float := #[0.6, 0.4]
  let likeA0 : Array (Array Float) := #[#[0.9, 0.1], #[0.2, 0.8]]
  let likeA1 : Array (Array Float) := #[#[0.3, 0.7], #[0.8, 0.2]]
  let like : Array (Array (Array Float)) := #[likeA0, likeA1]
  let m : DiscreteModel := { ns := 2, no := 2, na := 2, prior := prior, like := like }
  let pref : Preferences := { prefObs? := some #[0.8, 0.2] }
  let post0 := posterior m 0 0
  let f0 := freeEnergy m 0 0
  let e0 := efe m pref 0
  let e1 := efe m pref 1
  let best := bestAction m pref
  let ig0 := infoGain m 0
  let ig1 := infoGain m 1
  let best2 := bestPolicy2 m pref
  IO.println s!"posterior(a=0, obs=0) = {post0}"
  IO.println s!"F(a=0, obs=0) = {f0}"
  IO.println s!"EFE(a=0) = {e0}; EFE(a=1) = {e1}; best={best}"
  IO.println s!"IG(a=0) = {ig0}; IG(a=1) = {ig1}; best2={best2}"

end CLI
end HeytingLean

def main : IO Unit :=
  HeytingLean.CLI.QActiveInfer.run
