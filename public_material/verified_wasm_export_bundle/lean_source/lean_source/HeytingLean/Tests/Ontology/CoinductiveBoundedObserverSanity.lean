import HeytingLean.Ontology.CoinductiveBounded

/-!
# Tests.Ontology.CoinductiveBoundedObserverSanity

Compile-time sanity checks for the ontology observer layer.
-/

namespace HeytingLean.Tests.Ontology

open HeytingLean.Ontology.CoinductiveBounded
open HeytingLean.Genesis

def emptyChoices : ChoicePath 0 := fun i => nomatch i

noncomputable def liftedLifeObserver : Observer GraphCarrier GraphSignal :=
  Observer.ofBoundedObservation (graphBoundedObservation 0) CoGame.Life emptyChoices

#check ChoicePath
#check StabilizesAt
#check Observer
#check Observer.toBoundedObservation
#check graphObserver
#check observerWitnessSection

example :
    liftedLifeObserver.depth = 0 :=
  rfl

example :
    liftedLifeObserver.completedChoices = fun _ => false :=
  rfl

example :
    liftedLifeObserver.toBoundedObservation = graphBoundedObservation 0 := by
  simp [liftedLifeObserver]

example :
    liftedLifeObserver.toBoundedObservation.observe CoGame.Life = boundedObserveGraph 0 CoGame.Life := by
  rfl

example :
    liftedLifeObserver.toBoundedObservation.observe liftedLifeObserver.carrier =
      (liftedLifeObserver.contexts (liftedLifeObserver.depth + 1)).observe liftedLifeObserver.carrier := by
  exact Observer.stabilization_on_erased_image liftedLifeObserver

example :
    (observerWitnessSection liftedLifeObserver).1 = CoGame.Life := by
  rfl

example :
    PerspectivalPlenum.LensSheaf.ExistsInPlenum CoGame.Life := by
  exact observer_is_local_section liftedLifeObserver

example (choices : ChoicePath 0)
    (hstab : boundedObserveGraph 0 CoGame.Life = boundedObserveGraph 1 CoGame.Life) :
    (graphObserver CoGame.Life 0 choices hstab).toBoundedObservation = graphBoundedObservation 0 := by
  exact graphObserver_forget_eq CoGame.Life 0 choices hstab

end HeytingLean.Tests.Ontology
