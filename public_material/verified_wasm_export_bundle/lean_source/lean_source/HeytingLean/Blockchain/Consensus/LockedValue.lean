import HeytingLean.Blockchain.Bridge.LockedValue

/-
# Consensus.LockedValue

Consensus-level semantic target for the bridge-security row
“Locked Value Conservation” from `crypto_proofs_master_list.md`.

We reuse the minimal bridge locked-value model and its bundled
`LockedValueConservationStatement` as the meaning of the consensus
property.
-/

namespace HeytingLean
namespace Blockchain
namespace Consensus
namespace LockedValue

open HeytingLean.Blockchain.Bridge

/-- Semantic statement for locked-value conservation at the consensus
    level. -/
def Statement : Prop :=
  Bridge.LockedValue.LockedValueConservationStatement

/-- `Statement` holds via the underlying bridge locked-value theorem. -/
theorem statement_holds : Statement :=
  Bridge.LockedValue.lockedValueConservationStatement_holds

end LockedValue
end Consensus
end Blockchain
end HeytingLean

