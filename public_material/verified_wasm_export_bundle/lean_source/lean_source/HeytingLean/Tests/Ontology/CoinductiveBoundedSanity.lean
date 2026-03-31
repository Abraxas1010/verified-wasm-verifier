import HeytingLean.Ontology.CoinductiveBounded

namespace HeytingLean.Tests.Ontology

open HeytingLean.Ontology.CoinductiveBounded
open HeytingLean.Genesis

#check CarrierBackend
#check ObservationContext
#check BoundedObservation
#check StabilizedMeaning
#check fromCoGame
#check fromCoalgebra
#check boundedObserveGraph
#check fromGraphToStabilized
#check fromCoalgebraToStabilized

example : lifeWitness.backend = .graph :=
  lifeWitness_backend

example : coalgebraWitness.backend = .coalgebra :=
  coalgebraWitness_backend

example : CoGame.Bisim (cycleCoGame 0) CoGame.Life :=
  (bounded_projection_preserves_cycle_witness 2).1

example : boundedObserveGraph 2 (cycleCoGame 0) = boundedObserveGraph 2 CoGame.Life :=
  (bounded_projection_preserves_cycle_witness 2).2

example : (boundedObserveGraph 2 (cycleCoGame 2)).1 = .void :=
  cycleWitness_head_is_void

example : 0 ∈ (fromGraphToStabilized (boundedObserveGraph 0 CoGame.Life)).witness :=
  lifeWitness_support_nonempty

example : 0 ∈ (fromCoalgebraToStabilized 1 false [true]).witness :=
  coalgebraWitness_support_nonempty

example (w : List Bool) :
    (CoalgebraExamples.wordObservation 0).observe false w = false := by
  simpa using CoalgebraExamples.wordObservation_depth_zero false w

example (w : List Bool) :
    (CoalgebraExamples.wordObservation 1).observe false (true :: w) = true := by
  simpa using CoalgebraExamples.wordObservation_false_true w

end HeytingLean.Tests.Ontology
