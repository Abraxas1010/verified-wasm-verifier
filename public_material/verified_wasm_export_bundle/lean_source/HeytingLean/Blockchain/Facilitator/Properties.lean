import HeytingLean.Blockchain.Facilitator.Settlement

/-!
# Blockchain.Facilitator.Properties

Security properties of the facilitator core.
-/

namespace HeytingLean
namespace Blockchain
namespace Facilitator

theorem non_custodial (chain : ChainView) (vp : ValidPayload chain)
    (addr : Address) (hSender : addr ≠ vp.signed.data.sender) (hRecip : addr ≠ vp.signed.data.recipient) :
    (settle chain vp).balance addr = chain.balance addr := by
  simp [settle, hSender, hRecip]

theorem exact_transfer_sender (chain : ChainView) (vp : ValidPayload chain) :
    (settle chain vp).balance vp.signed.data.sender =
      chain.balance vp.signed.data.sender - vp.signed.data.amount := by
  simp [settle]

theorem exact_transfer_recipient (chain : ChainView) (vp : ValidPayload chain) :
    (settle chain vp).balance vp.signed.data.recipient =
      chain.balance vp.signed.data.recipient + vp.signed.data.amount := by
  have hRecNe : vp.signed.data.recipient ≠ vp.signed.data.sender := by
    intro h
    exact vp.sender_ne_recipient h.symm
  simp [settle, hRecNe]

theorem nonce_increment (chain : ChainView) (vp : ValidPayload chain) :
    (settle chain vp).nonce vp.signed.data.sender = chain.nonce vp.signed.data.sender + 1 := by
  simp [settle]

theorem nonce_unchanged_of_ne_sender (chain : ChainView) (vp : ValidPayload chain)
    (addr : Address) (h : addr ≠ vp.signed.data.sender) :
    (settle chain vp).nonce addr = chain.nonce addr := by
  simp [settle, h]

theorem no_replay (chain : ChainView) (vp : ValidPayload chain) :
    let chain' := settle chain vp
    ∀ (vp' : ValidPayload chain'), vp'.signed.data = vp.signed.data → False := by
  intro chain' vp' hData
  have hNonce' : chain'.nonce vp.signed.data.sender = vp.signed.data.nonce := by
    -- `vp'.nonce_match : chain'.nonce vp'.signed.data.sender = vp'.signed.data.nonce`
    simpa [hData] using vp'.nonce_match
  have hStep : chain'.nonce vp.signed.data.sender = chain.nonce vp.signed.data.sender + 1 := by
    -- unfold `chain'`
    simp [chain', settle]
  have hEq : chain.nonce vp.signed.data.sender + 1 = vp.signed.data.nonce := by
    simpa [hStep] using hNonce'
  have hEq' : vp.signed.data.nonce + 1 = vp.signed.data.nonce := by
    -- rewrite the LHS using `vp.nonce_match : chain.nonce sender = nonce`
    have hEq0 := hEq
    simp [vp.nonce_match] at hEq0
  have hSucc : Nat.succ vp.signed.data.nonce = vp.signed.data.nonce :=
    (Nat.succ_eq_add_one _).trans hEq'
  exact (Nat.succ_ne_self _ hSucc)

theorem conservation (chain : ChainView) (vp : ValidPayload chain) :
    let chain' := settle chain vp
    chain'.balance vp.signed.data.sender + chain'.balance vp.signed.data.recipient =
      chain.balance vp.signed.data.sender + chain.balance vp.signed.data.recipient := by
  intro chain'
  have hRecNe : vp.signed.data.recipient ≠ vp.signed.data.sender := by
    intro h
    exact vp.sender_ne_recipient h.symm
  -- unfold the two updated balances and then use `Nat.sub_add_cancel` (requires sufficient funds).
  have hLe : vp.signed.data.amount ≤ chain.balance vp.signed.data.sender := vp.balance_sufficient
  calc
    chain'.balance vp.signed.data.sender + chain'.balance vp.signed.data.recipient
        = (chain.balance vp.signed.data.sender - vp.signed.data.amount) +
            (chain.balance vp.signed.data.recipient + vp.signed.data.amount) := by
              simp [chain', settle, hRecNe]
    _ = (chain.balance vp.signed.data.sender - vp.signed.data.amount) +
          (vp.signed.data.amount + chain.balance vp.signed.data.recipient) := by
          simp [Nat.add_comm]
    _ = ((chain.balance vp.signed.data.sender - vp.signed.data.amount) + vp.signed.data.amount) +
          chain.balance vp.signed.data.recipient := by
          simp [Nat.add_assoc]
    _ = chain.balance vp.signed.data.sender + chain.balance vp.signed.data.recipient := by
          simp [Nat.sub_add_cancel hLe]

theorem auth_required (chain : ChainView) (sp : SignedPayload) :
    sp.signatureOk = false → ¬ ∃ (vp : ValidPayload chain), vp.signed = sp := by
  intro hInvalid hExists
  rcases hExists with ⟨vp, hEq⟩
  have : sp.signatureOk = true := by
    -- `vp.sig_valid : vp.signed.signatureOk = true`
    simpa [hEq] using vp.sig_valid
  -- Contradiction: a Bool cannot be both true and false.
  cases hInvalid.symm.trans this

end Facilitator
end Blockchain
end HeytingLean
