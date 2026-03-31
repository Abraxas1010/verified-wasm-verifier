import HeytingLean.Blockchain.Bridge.MessageModel

/-
# Consensus.MessagePassing

Consensus-level semantic targets for the bridge rows
`messagePassingSafety` and `replayAttackPrevention` from
`Blockchain.Consensus.Spec.PropertyId`, built on top of the minimal
bridge message-passing model.

The safety statement asserts that bridge invariants are preserved along
any sequence of delivery attempts (`MessagePassingSafetyStatement`),
while the replay-prevention statement isolates the duplicate-freedom
aspect (`ReplayPreventionStatement`).
-/

namespace HeytingLean
namespace Blockchain
namespace Consensus
namespace MessagePassing

/-- Semantic statement for `Spec.PropertyId.messagePassingSafety`:
    any sequence of delivery attempts starting from a state satisfying
    `Invariants` yields a state that still satisfies `Invariants`. -/
abbrev MessagePassingSafetyStatement : Prop :=
  HeytingLean.Blockchain.Bridge.MessageModel.MessagePassingSafetyStatement

/-- Semantic statement for `Spec.PropertyId.replayAttackPrevention`:
    delivered messages remain duplicate-free along any run of delivery
    attempts from a well-formed state. -/
abbrev ReplayPreventionStatement : Prop :=
  HeytingLean.Blockchain.Bridge.MessageModel.ReplayPreventionStatement

/-- `MessagePassingSafetyStatement` holds via the underlying bridge
    model theorem. -/
theorem messagePassingSafetyStatement_holds :
    MessagePassingSafetyStatement :=
  HeytingLean.Blockchain.Bridge.MessageModel.messagePassingSafetyStatement_holds

/-- `ReplayPreventionStatement` holds via the underlying bridge model
    theorem. -/
theorem replayPreventionStatement_holds :
    ReplayPreventionStatement :=
  HeytingLean.Blockchain.Bridge.MessageModel.replayPreventionStatement_holds

end MessagePassing
end Consensus
end Blockchain
end HeytingLean
