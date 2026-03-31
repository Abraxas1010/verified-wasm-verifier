import HeytingLean.Blockchain.Consensus.Core

/-
# Consensus.InfraExample

A minimal example execution exercising the infra-level consensus predicates
`GossipProtocolSafety`, `EclipseAttackResistance`, and `DosResistance`
defined in `Consensus.Core`.

In this model, all honest nodes share the same non-empty chain at each
time, and the chain length grows linearly with the time index, so all
three predicates hold.
-/

namespace HeytingLean
namespace Blockchain
namespace Consensus
namespace InfraExample

open Core

/-- An example infra execution where every honest node's chain at time `t` is
    exactly `List.range (t + 1)`, representing a genesis block together
    with `t` additional blocks. All nodes are honest. -/
def infraExecution : Execution :=
  { chainAt := fun t _ => List.range (t + 1)
    , honest := fun _ => True }

/-- `infraExecution` satisfies `GossipProtocolSafety`: all honest nodes
    see the same chain at each time. -/
theorem infraExecution_gossipSafe :
    Core.GossipProtocolSafety infraExecution := by
  intro t n₁ n₂ _ _
  -- Chains are independent of the node identifier.
  simp [infraExecution]

/-- `infraExecution` satisfies `EclipseAttackResistance`: honest nodes
    never see the empty chain; there is always at least a genesis
    block. -/
theorem infraExecution_eclipseResistant :
    Core.EclipseAttackResistance infraExecution := by
  intro t n _ hEmpty
  -- `List.range (t + 1)` is never empty.
  -- `List.range (t + 1)` has length `t + 1`, so it cannot be empty.
  have hLen : (infraExecution.chainAt t n).length = t + 1 := by
    simp [infraExecution]
  have hZero : (infraExecution.chainAt t n).length = 0 := by
    simp [hEmpty]
  have hContr : t + 1 = 0 := by
    have hZero' := hZero
    simp [hLen] at hZero'
  exact Nat.succ_ne_zero _ hContr

/-- `infraExecution` satisfies `DosResistance`: chain length for any
    honest node at time `t` is exactly `t + 1`, so in particular it is
    bounded by `t + 1`. -/
theorem infraExecution_dosResistant :
    Core.DosResistance infraExecution := by
  intro t n _
  -- Chains are `List.range (t + 1)`.
  have hLen : (infraExecution.chainAt t n).length = t + 1 := by
    simp [infraExecution]
  -- Rewrite and use reflexivity.
  simp [hLen]

/-- Registry-level instance: the `gossipProtocolSafety` row holds for
    `infraExecution`. -/
theorem propertyHolds_gossipProtocolSafety_infraExecution :
    Core.propertyHolds infraExecution
      HeytingLean.Blockchain.Consensus.Spec.PropertyId.gossipProtocolSafety := by
  have h : Core.GossipProtocolSafety infraExecution :=
    infraExecution_gossipSafe
  simpa [Core.propertyHolds] using h

/-- Registry-level instance: the `eclipseAttackResistance` row holds for
    `infraExecution`. -/
theorem propertyHolds_eclipseAttackResistance_infraExecution :
    Core.propertyHolds infraExecution
      HeytingLean.Blockchain.Consensus.Spec.PropertyId.eclipseAttackResistance := by
  have h : Core.EclipseAttackResistance infraExecution :=
    infraExecution_eclipseResistant
  simpa [Core.propertyHolds] using h

/-- Registry-level instance: the `dosResistance` row holds for
    `infraExecution`. -/
theorem propertyHolds_dosResistance_infraExecution :
    Core.propertyHolds infraExecution
      HeytingLean.Blockchain.Consensus.Spec.PropertyId.dosResistance := by
  have h : Core.DosResistance infraExecution :=
    infraExecution_dosResistant
  simpa [Core.propertyHolds] using h

end InfraExample
end Consensus
end Blockchain
end HeytingLean
