import HeytingLean.BountyHunter.AlgebraIR.Types

/-!
# HeytingLean.BountyHunter.AlgebraIR.Examples

Canonical tiny graphs used to de-risk Phase 0:

- `etherStoreVuln`: boundary call happens **before** the storage write (fails CEI).
- `etherStoreFixed`: storage write happens **before** the boundary call (passes CEI).

These examples are intentionally small and “hand-written” so the executable can be
tested without any Yul parser/translator.
-/

namespace HeytingLean.BountyHunter.AlgebraIR

private def op (s : String) : Op := { tag := s }

private def n (id : NodeId) (tag : String) (succs : Array NodeId)
    (effects : Array Effect := #[]) : Node :=
  { id := id, op := op tag, succs := succs, effects := effects }

/-- Vulnerable EtherStore-shaped CFG:
`boundaryCall` occurs before `storageWrite(slot)`. -/
def etherStoreVuln (slot : Nat := 0) : Graph :=
  { entry := 0
    exits := #[7, 8]
    nodes := #[
      n 0 "entry" #[1]
    , n 1 "sload" #[2] #[Effect.storageRead slot]
    , n 2 "gt" #[3]
    , n 3 "require" #[5, 8]  -- success → call, fail → revert
    , n 5 "call" #[6] #[Effect.boundaryCall "attacker"]
    , n 6 "sstore" #[7] #[Effect.storageWrite slot]
    , n 7 "return" #[]
    , n 8 "revert" #[]
    ] }

/-- Fixed EtherStore-shaped CFG:
`storageWrite(slot)` dominates `boundaryCall`. -/
def etherStoreFixed (slot : Nat := 0) : Graph :=
  { entry := 0
    exits := #[7, 8]
    nodes := #[
      n 0 "entry" #[1]
    , n 1 "sload" #[2] #[Effect.storageRead slot]
    , n 2 "gt" #[3]
    , n 3 "require" #[4, 8]  -- success → write, fail → revert
    , n 4 "sstore" #[5] #[Effect.storageWrite slot]
    , n 5 "call" #[7] #[Effect.boundaryCall "attacker"]
    , n 7 "return" #[]
    , n 8 "revert" #[]
    ] }

end HeytingLean.BountyHunter.AlgebraIR

