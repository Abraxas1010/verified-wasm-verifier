import Mathlib.Data.Nat.Basic

/-!
# Blockchain.Facilitator.Core

Phase 3: a minimal “trustless facilitator” core.

The design goal is *correct-by-construction* settlement: the settlement function only accepts a
dependent `ValidPayload` value, so it is impossible (in Lean) to call settlement without proving
the usual preconditions (signature-valid, nonce match, sufficient funds, and sender ≠ recipient).

Crypto primitives and the blockchain interface are modeled abstractly: the core only consumes a
boolean “signature verified” bit and a chain view (balances + nonces).
-/

namespace HeytingLean
namespace Blockchain
namespace Facilitator

abbrev Address := Nat
abbrev Amount := Nat
abbrev Nonce := Nat

structure ChainView where
  balance : Address → Amount
  nonce : Address → Nonce

namespace ChainView

def withBalance (c : ChainView) (a : Address) (bal : Amount) : ChainView :=
  { c with balance := fun x => if x = a then bal else c.balance x }

def withNonce (c : ChainView) (a : Address) (n : Nonce) : ChainView :=
  { c with nonce := fun x => if x = a then n else c.nonce x }

end ChainView

structure PaymentData where
  sender : Address
  recipient : Address
  amount : Amount
  nonce : Nonce
  deriving DecidableEq, Repr

structure SignedPayload where
  data : PaymentData
  /-- Result of an external signature verification check. -/
  signatureOk : Bool
  deriving DecidableEq, Repr

/-- A *dependent* payload type: cannot be constructed without proofs of validity. -/
structure ValidPayload (chain : ChainView) where
  signed : SignedPayload
  sig_valid : signed.signatureOk = true
  nonce_match : chain.nonce signed.data.sender = signed.data.nonce
  balance_sufficient : signed.data.amount ≤ chain.balance signed.data.sender
  sender_ne_recipient : signed.data.sender ≠ signed.data.recipient

end Facilitator
end Blockchain
end HeytingLean

