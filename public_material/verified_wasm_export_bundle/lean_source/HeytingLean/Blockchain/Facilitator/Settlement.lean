import HeytingLean.Blockchain.Facilitator.Core

/-!
# Blockchain.Facilitator.Settlement

State transition for valid payments.
-/

namespace HeytingLean
namespace Blockchain
namespace Facilitator

def settle (chain : ChainView) (vp : ValidPayload chain) : ChainView :=
  let sender := vp.signed.data.sender
  let recipient := vp.signed.data.recipient
  let amount := vp.signed.data.amount
  { balance := fun a =>
      if a = sender then
        chain.balance a - amount
      else if a = recipient then
        chain.balance a + amount
      else
        chain.balance a
    nonce := fun a =>
      if a = sender then
        chain.nonce a + 1
      else
        chain.nonce a }

end Facilitator
end Blockchain
end HeytingLean
