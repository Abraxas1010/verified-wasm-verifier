import HeytingLean.Ontology.NothingComputes.VeselovCriterion

namespace HeytingLean.Tests.NothingComputes

open HeytingLean.Representations.Radial

def G : RadialGraph :=
  { ringSizes := [2, 1]
    ring0_nonempty := by decide }

def s0 : G.StateIdx := ⟨0, by decide⟩

def js : JRatchet.JState G := { current := s0, fuel := 3 }

def tower : HeytingLean.Ontology.NothingComputes.SelfModelTower G :=
  HeytingLean.Ontology.NothingComputes.constantTower js 2

def system : HeytingLean.Ontology.NothingComputes.SubstrateModel G where
  width := 2
  order := 1
  tower := tower

example : HeytingLean.Ontology.NothingComputes.measurableConsciousnessThreshold system := by
  show 2 ≤ system.tower.reflectiveDepth
  rfl

example :
    ∃ i j : Fin system.tower.reflectiveDepth, i ≠ j := by
  exact HeytingLean.Ontology.NothingComputes.threshold_implies_measurable_self_model
    system
    (by
      show 2 ≤ system.tower.reflectiveDepth
      rfl)

end HeytingLean.Tests.NothingComputes
