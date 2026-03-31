import HeytingLean.Topology.Knot.BracketMathlibReidemeisterR3

/-!
# Kauffman R3 Transition Sanity

Sanity checks for the scoped replacement of the over-strong unconditional R3
endpoint claim.
-/

namespace HeytingLean.Tests.Topology.KauffmanR3TransitionSanity

open HeytingLean.Topology.Knot
open Kauffman

#check r3SkeinStep_eq_of_bridge_witness
#check r3SkeinStep_eq_of_two_level_bridge_witness_endpoints
#check bracketGraphML_r3_invariant_of_two_level_bridge_witness_endpoints
#check r3SkeinStep_unconditional_goal_iff_bridge_witness_goal
#check bracketGraphML_unconditional_goal_iff_bridge_witness_goal

example {g gL gR : PDGraph} {x u w : Nat}
    (hLeft : Reidemeister.r3BraidLeft g x u w = .ok gL)
    (hRight : Reidemeister.r3BraidRight g x u w = .ok gR)
    (hTwo : R3TwoLevelBridgeWitness g x u w) :
    r3SkeinStep gL = r3SkeinStep gR := by
  exact r3SkeinStep_eq_of_two_level_bridge_witness_endpoints
    (g := g) (gL := gL) (gR := gR) (x := x) (u := u) (w := w)
    hLeft hRight hTwo

example :
    (∀ {g gL gR : PDGraph} {x u w : Nat},
      Reidemeister.r3BraidLeft g x u w = .ok gL →
      Reidemeister.r3BraidRight g x u w = .ok gR →
      r3SkeinStep gL = r3SkeinStep gR) →
    (∀ {g gL gR : PDGraph} {x u w : Nat},
      Reidemeister.r3BraidLeft g x u w = .ok gL →
      Reidemeister.r3BraidRight g x u w = .ok gR →
      R3SkeinBridgeWitness g gL gR x u w) := by
  intro h g gL gR x u w hLeft hRight
  exact (r3SkeinStep_unconditional_goal_iff_bridge_witness_goal).1 h hLeft hRight

example :
    (∀ {g gL gR : PDGraph} {x u w : Nat},
      Reidemeister.r3BraidLeft g x u w = .ok gL →
      Reidemeister.r3BraidRight g x u w = .ok gR →
      R3SkeinBridgeWitness g gL gR x u w) →
    (∀ {g gL gR : PDGraph} {x u w : Nat},
      Reidemeister.r3BraidLeft g x u w = .ok gL →
      Reidemeister.r3BraidRight g x u w = .ok gR →
      bracketGraphML gL = bracketGraphML gR) := by
  intro h g gL gR x u w hLeft hRight
  exact (bracketGraphML_unconditional_goal_iff_bridge_witness_goal).2 h hLeft hRight

end HeytingLean.Tests.Topology.KauffmanR3TransitionSanity

