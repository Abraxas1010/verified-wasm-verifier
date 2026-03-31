import HeytingLean.Topos.JRatchet

namespace HeytingLean.Ontology.NothingComputes

open HeytingLean.Representations.Radial

/-- A layered self-model tower over explicit J-ratchet states. -/
structure SelfModelTower (G : RadialGraph) where
  depth : Nat
  layer : Fin depth → JRatchet.JState G
  ratchet : ∀ i, HeytingLean.Topos.JRatchet.RatchetTrajectory
    (JRatchet.JState.spentFuel (layer i))

/-- The measurable reflective depth of the tower. -/
def SelfModelTower.reflectiveDepth {G : RadialGraph} (tower : SelfModelTower G) : Nat :=
  tower.depth

/-- A consciousness-style threshold starts once at least two self-model levels are present. -/
def SelfModelTower.multiLevel {G : RadialGraph} (tower : SelfModelTower G) : Prop :=
  2 ≤ tower.reflectiveDepth

/-- A constant tower is still meaningful because each layer keeps the explicit ratchet contract. -/
def constantTower {G : RadialGraph} (js : JRatchet.JState G) (depth : Nat) :
    SelfModelTower G where
  depth := depth
  layer _ := js
  ratchet _ := HeytingLean.Topos.JRatchet.radial_spentFuel_trajectory (js := js)

theorem constantTower_reflectiveDepth {G : RadialGraph} (js : JRatchet.JState G) (depth : Nat) :
    (constantTower js depth).reflectiveDepth = depth := rfl

theorem positive_depth_has_layer {G : RadialGraph} (tower : SelfModelTower G)
    (h : 0 < tower.reflectiveDepth) :
    ∃ i : Fin tower.reflectiveDepth,
      HeytingLean.Topos.JRatchet.RatchetTrajectory
        (JRatchet.JState.spentFuel (tower.layer i)) := by
  refine ⟨⟨0, h⟩, tower.ratchet ⟨0, h⟩⟩

theorem multiLevel_has_two_layers {G : RadialGraph} (tower : SelfModelTower G)
    (h : tower.multiLevel) :
    ∃ i j : Fin tower.reflectiveDepth, i ≠ j := by
  have h0 : 0 < tower.reflectiveDepth := lt_of_lt_of_le (by decide : 0 < 2) h
  have h1 : 1 < tower.reflectiveDepth := lt_of_lt_of_le (by decide : 1 < 2) h
  refine ⟨⟨0, h0⟩, ⟨1, h1⟩, ?_⟩
  intro hij
  have : (0 : Nat) = 1 := congrArg Fin.val hij
  exact Nat.zero_ne_one this

end HeytingLean.Ontology.NothingComputes
