import Mathlib.Data.List.Basic

/-
# Blockchain.Bridge.LockedValue

Minimal locked-value conservation model for cross-chain bridges.

We track an L1 "locked" balance and an L2 "minted" balance for a single
asset, together with operations that lock-and-mint or burn-and-release
that asset. The main invariant is that the total amount locked on L1 is
always equal to the total amount minted on L2.
-/

namespace HeytingLean
namespace Blockchain
namespace Bridge
namespace LockedValue

/-- Bridge state: total locked value on L1 and total minted value on L2. -/
structure State where
  l1Locked : Nat
  l2Minted : Nat
  deriving Repr, Inhabited

/-- Operation kind: either lock on L1 and mint on L2, or burn on L2 and
    release on L1. -/
inductive OpKind
  | lockAndMint
  | burnAndRelease
  deriving DecidableEq, Repr

/-- Bridge operation with a kind and non-negative amount. -/
structure Op where
  kind   : OpKind
  amount : Nat
  deriving Repr

/-- Locked-value invariant: L2 minted supply equals L1 locked value. -/
def LockedValueInvariant (st : State) : Prop :=
  st.l1Locked = st.l2Minted

/-- Apply a single bridge operation.

* `lockAndMint` increases both `l1Locked` and `l2Minted` by the same
  amount.
* `burnAndRelease` decreases both `l1Locked` and `l2Minted` by the same
  amount (truncated subtraction on `Nat`). -/
def applyOp (st : State) (op : Op) : State :=
  let δ := op.amount
  match op.kind with
  | .lockAndMint =>
      { st with
        l1Locked := st.l1Locked + δ
        l2Minted := st.l2Minted + δ }
  | .burnAndRelease =>
      { st with
        l1Locked := st.l1Locked - δ
        l2Minted := st.l2Minted - δ }

/-- Run a sequence of bridge operations by folding `applyOp`. -/
def runOps (st : State) (ops : List Op) : State :=
  ops.foldl applyOp st

section Lemmas

variable {st : State} {op : Op} {ops : List Op}

/-- Single-step preservation of the locked-value invariant. -/
lemma applyOp_preserves_invariant
    (hInv : LockedValueInvariant st) :
    LockedValueInvariant (applyOp st op) := by
  classical
  -- Case split on the operation and its amount.
  cases op with
  | mk kind amount =>
      cases kind with
      | lockAndMint =>
          -- Both fields add `amount`.
          have hEq :
              st.l1Locked + amount = st.l2Minted + amount :=
            congrArg (fun x => x + amount) hInv
          simpa [LockedValueInvariant, applyOp] using hEq
      | burnAndRelease =>
          -- Both fields subtract `amount` (truncated on `Nat`).
          have hEq :
              st.l1Locked - amount = st.l2Minted - amount :=
            congrArg (fun x => x - amount) hInv
          simpa [LockedValueInvariant, applyOp] using hEq

/-- Multi-step preservation of the locked-value invariant. -/
lemma runOps_preserves_invariant
    (st : State) (ops : List Op) :
    LockedValueInvariant st →
    LockedValueInvariant (runOps st ops) := by
  classical
  induction ops generalizing st with
  | nil =>
      intro hInv
      simpa [runOps] using hInv
  | cons op ops ih =>
      intro hInv
      -- First step preserves the invariant.
      have hStep : LockedValueInvariant (applyOp st op) :=
        applyOp_preserves_invariant (st := st) (op := op) hInv
      -- Tail of the list preserves the invariant from the updated state.
      have hTail :
          LockedValueInvariant (runOps (applyOp st op) ops) :=
        ih (st := applyOp st op) hStep
      simpa [runOps, List.foldl] using hTail

end Lemmas

/-- Bundled locked-value conservation statement: any sequence of bridge
    operations preserves the invariant that L2 minted supply equals L1
    locked value. -/
def LockedValueConservationStatement : Prop :=
  ∀ st ops, LockedValueInvariant st → LockedValueInvariant (runOps st ops)

/-- `LockedValueConservationStatement` holds for the minimal bridge
    locked-value model. -/
theorem lockedValueConservationStatement_holds :
    LockedValueConservationStatement := by
  intro st ops hInv
  exact runOps_preserves_invariant st ops hInv

end LockedValue
end Bridge
end Blockchain
end HeytingLean
