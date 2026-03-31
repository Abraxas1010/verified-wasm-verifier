import Mathlib.Data.List.Basic

/-
# Blockchain.Bridge.MessageModel

Minimal message-passing model for cross-chain bridges, used as a
semantic backbone for `messagePassingSafety` and
`replayAttackPrevention` consensus properties.

The focus here is a small state machine with:
* a set of sent messages; and
* a set of delivered messages;
together with invariants stating that deliveries do not introduce
duplicates or forged messages.
-/

namespace HeytingLean
namespace Blockchain
namespace Bridge
namespace MessageModel

/-- Chain identifiers for this minimal bridge model. -/
abbrev ChainId := Nat

/-- Message identifiers. -/
abbrev MsgId := Nat

/-- Payloads are kept abstract at this level. -/
abbrev Payload := String

/-- A simple cross-chain message: identifier, source/destination chain,
    and a payload. -/
structure Message where
  id      : MsgId
  src     : ChainId
  dst     : ChainId
  payload : Payload
  deriving Repr, DecidableEq

/-- Bridge state: messages that have been sent and those that have been
    delivered so far. We do not model time or ordering explicitly; those
    aspects are delegated to higher-level executions. -/
structure State where
  sent      : List Message
  delivered : List Message
  deriving Repr

/-- Invariant describing a well-formed bridge state:

* no delivered message is duplicated; and
* every delivered message was previously sent.

This captures the safety aspect “no duplicate or forged messages”. -/
def Invariants (st : State) : Prop :=
  st.delivered.Nodup ∧
    ∀ m, m ∈ st.delivered → m ∈ st.sent

/-- Single-step delivery: if the message has been sent and not yet
    delivered, add it to the head of the `delivered` list; otherwise
    leave the state unchanged. -/
def deliver (st : State) (m : Message) : State :=
  if m ∈ st.sent then
    if m ∈ st.delivered then
      st
    else
      { st with delivered := m :: st.delivered }
  else
    st

/-- Iterate `deliver` over a list of messages, modelling a batch of
    delivery attempts. -/
def runDeliveries (st : State) (ms : List Message) : State :=
  ms.foldl deliver st

section Lemmas

variable {st : State} {m : Message} {ms : List Message}

/-- A helper lemma: if a message is newly added to a list that does not
    contain it, finiteness implies the resulting list is `Nodup` iff the
    original list was. -/
lemma nodup_cons_of_not_mem
    (hMem : m ∉ st.delivered) :
    List.Nodup st.delivered →
      List.Nodup (m :: st.delivered) := by
  intro hNodup
  exact List.nodup_cons.mpr ⟨hMem, hNodup⟩

/-- `deliver` preserves the bridge invariants. -/
lemma deliver_preserves_invariants
    (hInv : Invariants st) :
    Invariants (deliver st m) := by
  classical
  rcases hInv with ⟨hNodup, hSent⟩
  by_cases hSentMem : m ∈ st.sent
  · -- The message has been sent; check whether it is already delivered.
    by_cases hDeliveredMem : m ∈ st.delivered
    · -- Already delivered: state is unchanged.
      have hEq : deliver st m = st := by
        simp [deliver, hSentMem, hDeliveredMem]
      simpa [hEq] using And.intro hNodup hSent
    · -- Newly delivered case: `m` was sent and not yet delivered.
      have hNotDelivered : m ∉ st.delivered := hDeliveredMem
      -- In this branch we actually deliver `m`.
      have hEq :
          deliver st m =
            { st with delivered := m :: st.delivered } := by
        simp [deliver, hSentMem, hNotDelivered]
      -- `delivered` remains `Nodup` after consing `m`.
      have hNodup' :
          (m :: st.delivered).Nodup :=
        nodup_cons_of_not_mem (st := st) (m := m) hNotDelivered hNodup
      -- Any element of the new `delivered` list was sent.
      have hSent' :
          ∀ m', m' ∈ (m :: st.delivered) → m' ∈ st.sent := by
        intro m' hMem'
        simp at hMem'
        rcases hMem' with hEq' | hMemOld
        · -- `m'` is exactly `m`, which is in `st.sent`.
          simpa [hEq'] using hSentMem
        · -- `m'` was already delivered before, so use the invariant.
          exact hSent m' hMemOld
      have hInv' :
          Invariants { st with delivered := m :: st.delivered } :=
        And.intro hNodup' hSent'
      simpa [hEq] using hInv'
  · -- Message not sent: the state is unchanged.
    have hEq : deliver st m = st := by
      simp [deliver, hSentMem]
    simpa [hEq] using And.intro hNodup hSent

/-- `runDeliveries` preserves the bridge invariants. -/
lemma runDeliveries_preserves_invariants
    (st : State) (ms : List Message) :
    Invariants st →
    Invariants (runDeliveries st ms) := by
  classical
  induction ms generalizing st with
  | nil =>
      intro hInv
      simpa [runDeliveries] using hInv
  | cons m ms ih =>
      intro hInv
      -- First step preserves invariants.
      have hStep : Invariants (deliver st m) :=
        deliver_preserves_invariants (st := st) (m := m) hInv
      -- Then the tail of the list preserves invariants starting from
      -- the updated state.
      have hTail :
          Invariants (runDeliveries (deliver st m) ms) :=
        ih (st := deliver st m) hStep
      simpa [runDeliveries, List.foldl] using hTail

end Lemmas

/-- Bundled message-passing safety statement: any sequence of delivery
    attempts, starting from a state satisfying `Invariants`, yields a
    state in which `Invariants` still holds. -/
def MessagePassingSafetyStatement : Prop :=
  ∀ st ms, Invariants st → Invariants (runDeliveries st ms)

/-- Bundled replay-prevention statement: as a corollary of the safety
    invariants, delivered messages remain duplicate-free throughout any
    run of delivery attempts. -/
def ReplayPreventionStatement : Prop :=
  ∀ st ms, Invariants st →
    (runDeliveries st ms).delivered.Nodup

/-- `MessagePassingSafetyStatement` holds for the minimal bridge model. -/
theorem messagePassingSafetyStatement_holds :
    MessagePassingSafetyStatement := by
  intro st ms hInv
  exact runDeliveries_preserves_invariants (st := st) (ms := ms) hInv

/-- `ReplayPreventionStatement` holds as a direct consequence of
    `MessagePassingSafetyStatement`. -/
theorem replayPreventionStatement_holds :
    ReplayPreventionStatement := by
  intro st ms hInv
  have h :=
    messagePassingSafetyStatement_holds (st := st) (ms := ms) hInv
  -- Extract the `Nodup` component of the invariants.
  exact h.left

end MessageModel
end Bridge
end Blockchain
end HeytingLean
