import HeytingLean.ATP.LaneChanging
import HeytingLean.PathIntegral.Measure

/-!
# ATP.FreeEnergySearch

Free-energy-guided proof search scaffolding.

This file records a minimal numerical objective for “expected free energy” and a decision rule
that can trigger lane changes. It is deliberately lightweight and executable.
-/

namespace HeytingLean
namespace ATP

open HeytingLean.Embeddings

/-- Beliefs about search progress as Float-valued lane-local stuck costs. -/
structure ProofBeliefs where
  stuckProbability : LensID → Float := fun _ => 0.0

/-- A small depth-based free-energy baseline for a proof position. -/
def proofFreeEnergy (pos : ProofPosition) : Float :=
  Float.ofNat pos.depth

/-- Information-loss cost of changing from the current lens to `newLens`. -/
def laneChangeTransportCost (pos : ProofPosition) (newLens : LensID) : Float :=
  PathIntegral.lensTransitionFactorFloat pos.lens newLens

/-- Expected free energy of *staying* in the current lens. -/
def expectedFreeEnergyStay (beliefs : ProofBeliefs) (pos : ProofPosition) : Float :=
  proofFreeEnergy pos + beliefs.stuckProbability pos.lens

/-- Expected free energy of *changing* to a new lens. -/
def expectedFreeEnergyChange (beliefs : ProofBeliefs) (pos : ProofPosition) (newLens : LensID) : Float :=
  proofFreeEnergy pos +
    beliefs.stuckProbability newLens +
    laneChangeTransportCost pos newLens

/-- Select whether to change lanes based on expected free energy. -/
def selectLane (beliefs : ProofBeliefs) (pos : ProofPosition) : LaneDecision :=
  let newLens := nextLens pos.lens
  if expectedFreeEnergyChange beliefs pos newLens < expectedFreeEnergyStay beliefs pos then
    .switch newLens
  else
    .stay

theorem selectLane_switch_of_change_lt_stay (beliefs : ProofBeliefs) (pos : ProofPosition)
    (h :
      expectedFreeEnergyChange beliefs pos (nextLens pos.lens) <
        expectedFreeEnergyStay beliefs pos) :
    selectLane beliefs pos = .switch (nextLens pos.lens) := by
  unfold selectLane
  simp [h]

theorem selectLane_stay_of_change_not_lt (beliefs : ProofBeliefs) (pos : ProofPosition)
    (h :
      ¬ expectedFreeEnergyChange beliefs pos (nextLens pos.lens) <
        expectedFreeEnergyStay beliefs pos) :
    selectLane beliefs pos = .stay := by
  unfold selectLane
  simp [h]

def baselineBeliefs : ProofBeliefs := {
  stuckProbability := fun _ => 0.0
}

def omegaPressureBeliefs : ProofBeliefs := {
  stuckProbability := fun lens =>
    if lens = .omega then
      4.0
    else
      0.0
}

def omegaPosition : ProofPosition := {
  lens := .omega
  depth := 0
  history := []
}

example :
    expectedFreeEnergyChange baselineBeliefs omegaPosition .region >
      expectedFreeEnergyChange baselineBeliefs omegaPosition .matula := by
  native_decide

example :
    expectedFreeEnergyChange baselineBeliefs omegaPosition .region >
      expectedFreeEnergyStay baselineBeliefs omegaPosition := by
  native_decide

example :
    selectLane baselineBeliefs omegaPosition = .stay := by
  apply selectLane_stay_of_change_not_lt
  native_decide

example :
    selectLane omegaPressureBeliefs omegaPosition = .switch .tensor := by
  apply selectLane_switch_of_change_lt_stay
  native_decide

end ATP
end HeytingLean
