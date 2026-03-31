import HeytingLean.Topos.JRatchet

namespace HeytingLean
namespace Bridges
namespace JRatchet

/-- All known J-ratchet variant kinds in HeytingLean.

Each variant produces a monotone level function (`RatchetTrajectory`)
that witnesses irreversible progression in its domain. -/
inductive JRatchetVariantTag where
  -- Tier 1: Core definitions
  | frameLevelCore
  | radialExploration
  | ratchetTrajectory
  -- Tier 2: StrictRatchet / PerspectivalPlenum
  | strictRatchetStage
  | ratchetStep
  | ratchetTower
  -- Tier 3: DimensionalRatchet
  | dimensionalRatchet
  | dimensionalRatchetTranslate
  | dimensionalRatchetLossProfile
  -- Tier 4: Domain bridges
  | assemblyRatchet
  | eigenformSoupRatchet
  | veselovGeneticCodeRatchet
  -- Tier 5: Structural
  | ratchetStepNucleus
  -- Tier 6: Literature extensions
  | pataraiaNuclearJoin
  | preRatchetStabilization
  | quanticRatchetStep
  | nuclearRangeRatchet
  | diegoFiniteness
  | dragalinRatchet
  | spatialityRatchet
  deriving Repr, DecidableEq

def allJRatchetTags : List JRatchetVariantTag :=
  [ .frameLevelCore
  , .radialExploration
  , .ratchetTrajectory
  , .strictRatchetStage
  , .ratchetStep
  , .ratchetTower
  , .dimensionalRatchet
  , .dimensionalRatchetTranslate
  , .dimensionalRatchetLossProfile
  , .assemblyRatchet
  , .eigenformSoupRatchet
  , .veselovGeneticCodeRatchet
  , .ratchetStepNucleus
  , .pataraiaNuclearJoin
  , .preRatchetStabilization
  , .quanticRatchetStep
  , .nuclearRangeRatchet
  , .diegoFiniteness
  , .dragalinRatchet
  , .spatialityRatchet
  ]

example : allJRatchetTags.length = 20 := by
  decide

end JRatchet
end Bridges
end HeytingLean
