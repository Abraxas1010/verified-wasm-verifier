import HeytingLean.Ontology.CoinductiveBounded

/-!
# Tests.Ontology.CoinductiveBoundedBackendIndependenceSanity

Compile-time sanity checks for the first backend-independence tranche.
-/

namespace HeytingLean.Tests.Ontology

open HeytingLean.Ontology.CoinductiveBounded
open HeytingLean.Genesis

#check SupportBehavior
#check ObservationBehaviorEquiv
#check core_vs_certified_support_route
#check stabilizedMeaning_transport_core
#check stabilizedMeaning_transport_certified

example :
    lifeDepthOneBehavior.backend = .graph :=
  rfl

example :
    bitFlipDepthOneBehavior.backend = .coalgebra :=
  rfl

example :
    ObservationBehaviorEquiv lifeDepthOneBehavior bitFlipDepthOneBehavior :=
  life_vs_bitFlip_behavior_equiv

example :
    (fromGraphToStabilized (boundedObserveGraph 1 CoGame.Life)).witness =
      HeytingLean.Nucleus.CertifiedFixedPoint.extract
        (certifyGraphSignal (boundedObserveGraph 1 CoGame.Life)) :=
  graphRoute_core_vs_certified 1 CoGame.Life

example :
    (fromCoalgebraToStabilized 1 false [true]).witness =
      HeytingLean.Nucleus.CertifiedFixedPoint.extract
        (certifyCoalgebraWord 1 false [true]) :=
  coalgebraRoute_core_vs_certified 1 false [true]

example :
    (fromGraphToStabilized (boundedObserveGraph 1 CoGame.Life)).witness =
      (fromCoalgebraToStabilized 1 false [true]).witness :=
  life_vs_bitFlip_stabilized_meaning_example

example :
    HeytingLean.Nucleus.CertifiedFixedPoint.extract
        (certifyGraphSignal (boundedObserveGraph 1 CoGame.Life)) =
      HeytingLean.Nucleus.CertifiedFixedPoint.extract
        (certifyCoalgebraWord 1 false [true]) :=
  life_vs_bitFlip_certified_example

end HeytingLean.Tests.Ontology
