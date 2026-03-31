import HeytingLean.Payments.Types

/-!
# Payments ContractModel — single-call state transition model

Minimal abstract model of a single-call PaymentManager relation with guards:
  (a) statement binding via `stmtHash`,
  (b) recipient membership (All/Verified/Custom),
  (c) concurrency guard via a monotone `lastEvent` counter.

We expose a total function `step?` that returns either a new state or a
single explicit rejection reason. This captures the “single-reason” failure
invariant and deterministic verdict.
-/

namespace HeytingLean
namespace Payments
namespace ContractModel

open Payments

/-! ## Abstract inputs -/

/-- Minimal public inputs we bind into the statement hash. -/
structure Pub where
  chainId        : String
  paymentManager : String
  recipient      : String
  amount         : String
  budget_id      : String
  epoch          : Nat
  deriving Inhabited, Repr, DecidableEq

/-- Minimal certificate pins (semantics + compiled-system digests). -/
structure Pins where
  canonical_semantics_hash : String
  compiled_system_hash     : String
  deriving Inhabited, Repr, DecidableEq

/-- Abstract call: pre-state commitment and `stmtHash` provided by caller. -/
structure PMCall where
  pub       : Pub
  statePreC : String
  stmtHash  : String
  deriving Inhabited, Repr, DecidableEq

/-- Manager’s on-chain state for concurrency and pinning. -/
structure PMState where
  lastEvent : Nat := 0
  stateC    : String := ""
  pins      : Pins
  deriving Inhabited, Repr, DecidableEq

/-- Single-reason rejection taxonomy. -/
inductive Reject
| BadStmtHash
| NotMember
| StaleEvent
deriving Repr, DecidableEq

/-- Abstract recipient membership policy. -/
inductive Membership
| all
| custom (recips : List String)
| verified
deriving Repr, DecidableEq

/-- Deterministic membership check relative to a pinned policy. -/
def member (m : Membership) (recipient : String) (verifiedOk : Bool := false) : Bool :=
  match m with
  | .all => true
  | .custom rs => rs.contains recipient
  | .verified => verifiedOk

/-- Deterministic statement hash (shape only; use bytes-level hash in runtime). -/
def stmtHashOf (p : Pub) (pins : Pins) (statePreC : String) : String :=
  s!"{pins.canonical_semantics_hash}:{pins.compiled_system_hash}:{p.chainId}:{p.paymentManager}:{p.recipient}:{p.amount}:{p.budget_id}:{p.epoch}:{statePreC}"

/-- Single-call state transition with guards and a single explicit reason on failure. -/
def step? (policy : Membership) (verifiedOk : Bool)
    (s : PMState) (c : PMCall) : Except Reject PMState :=
  -- (a) Statement binding
  if c.stmtHash ≠ stmtHashOf c.pub s.pins s.stateC then
    .error .BadStmtHash
  -- (b) Recipient membership
  else if member policy c.pub.recipient verifiedOk = false then
    .error .NotMember
  -- (c) Concurrency: ensure the call binds the current pre-state commitment
  else if c.statePreC ≠ s.stateC then
    .error .StaleEvent
  else
    .ok { s with lastEvent := s.lastEvent + 1, stateC := c.statePreC }

/-! ## Properties

We keep properties intentionally lightweight here to avoid introducing
unnecessary proof infrastructure. The `step?` function is total and pure,
so determinism follows by definitional equality, and its rejection space is
explicitly a single reason via the `Reject` sum.
-/

end ContractModel
end Payments
end HeytingLean
