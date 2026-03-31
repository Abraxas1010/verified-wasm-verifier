import HeytingLean.Genesis.YWitness.Foundations
import HeytingLean.Numbers.Surreal.LoFDerivation
import HeytingLean.Numbers.Surreal.ClosureReentry
import HeytingLean.Numbers.Surreal.ReentryFixedPoint

namespace HeytingLean.Numbers.Surreal.YWitness

open HeytingLean.Numbers.Surreal
open HeytingLean.Numbers.Surreal.LoFDerivation
open HeytingLean.Numbers.SurrealCore

/-- A staged "coin" packaging of a surreal pre-game as cut data plus a closure carrier. -/
structure GapPointCoin where
  raw : PreGame
  distinction : GameDistinction
  closureCarrier : Carrier

/-- Build the staged gap/point coin from a concrete pre-game. -/
def ofPreGame (g : PreGame) : GapPointCoin where
  raw := g
  distinction := GameDistinction.ofPreGame g
  closureCarrier := { h | h = SurrealCore.canonicalize g }

@[simp] theorem ofPreGame_raw (g : PreGame) : (ofPreGame g).raw = g := rfl

@[simp] theorem ofPreGame_inside (g : PreGame) :
    (ofPreGame g).distinction.inside = g.L := rfl

@[simp] theorem ofPreGame_outside (g : PreGame) :
    (ofPreGame g).distinction.outside = g.R := rfl

theorem distinction_roundtrip_on_raw_cut (g : PreGame) :
    (ofPreGame g).distinction.inside = g.L /\
      (ofPreGame g).distinction.outside = g.R := by
  exact ⟨rfl, rfl⟩

theorem canonicalized_mem_closureCarrier (g : PreGame) :
    SurrealCore.canonicalize g ∈ (ofPreGame g).closureCarrier := by
  simp [ofPreGame]

theorem surreal_gap_point_bridge (g : PreGame) :
    (ofPreGame g).distinction.inside = g.L /\
      (ofPreGame g).distinction.outside = g.R /\
      SurrealCore.canonicalize g ∈ (ofPreGame g).closureCarrier := by
  exact ⟨rfl, rfl, canonicalized_mem_closureCarrier g⟩

/-- Existing closure/reentry machinery already exhibits a nontrivial two-step cycle from the
empty carrier. -/
theorem surreal_reentry_two_step_cycle :
    oscillate (oscillate (∅ : Carrier)) = (∅ : Carrier) /\
      oscillate (∅ : Carrier) = canonicalCoreᶜ := by
  exact ⟨oscillate_twice_empty, oscillate_empty_eq_core_compl⟩

end HeytingLean.Numbers.Surreal.YWitness
