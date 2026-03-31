import HeytingLean.Blockchain.Facilitator.Core

/-!
# Blockchain.Facilitator.Validation

Computable construction of `ValidPayload` via decidable checks.
-/

namespace HeytingLean
namespace Blockchain
namespace Facilitator

def isValid (chain : ChainView) (sp : SignedPayload) : Prop :=
  sp.signatureOk = true ∧
    chain.nonce sp.data.sender = sp.data.nonce ∧
      sp.data.amount ≤ chain.balance sp.data.sender ∧
        sp.data.sender ≠ sp.data.recipient

instance (chain : ChainView) (sp : SignedPayload) : Decidable (isValid chain sp) := by
  unfold isValid
  infer_instance

def validate? (chain : ChainView) (sp : SignedPayload) : Option (ValidPayload chain) :=
  if hSig : sp.signatureOk = true then
    if hNonce : chain.nonce sp.data.sender = sp.data.nonce then
      if hBal : sp.data.amount ≤ chain.balance sp.data.sender then
        if hNe : sp.data.sender ≠ sp.data.recipient then
          some
            { signed := sp
              sig_valid := hSig
              nonce_match := hNonce
              balance_sufficient := hBal
              sender_ne_recipient := hNe }
        else
          none
      else
        none
    else
      none
  else
    none

theorem validate?_eq_some_iff (chain : ChainView) (sp : SignedPayload) :
    (∃ vp : ValidPayload chain, validate? chain sp = some vp) ↔ isValid chain sp := by
  classical
  unfold validate? isValid
  by_cases hSig : sp.signatureOk = true
  · by_cases hNonce : chain.nonce sp.data.sender = sp.data.nonce
    · by_cases hBal : sp.data.amount ≤ chain.balance sp.data.sender
      · by_cases hNe : sp.data.sender ≠ sp.data.recipient
        · simp [hSig, hNonce, hBal, hNe]
        · simp [hSig, hNonce, hBal, hNe]
      · simp [hSig, hNonce, hBal]
    · simp [hSig, hNonce]
  · simp [hSig]

end Facilitator
end Blockchain
end HeytingLean
