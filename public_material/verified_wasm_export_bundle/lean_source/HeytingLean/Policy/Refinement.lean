import HeytingLean.Policy.Recipients

namespace HeytingLean
namespace Policy

open RecipientSpec

structure Cert where
  recipients : RecipientSpec
  budget     : Nat
  startTs    : Nat
  endTs      : Nat
  deriving Repr

def refines (parent child : Cert) : Bool :=
  recipientRefines parent.recipients child.recipients &&
  Nat.ble child.budget parent.budget &&
  Nat.ble parent.startTs child.startTs &&
  Nat.ble child.endTs parent.endTs

end Policy
end HeytingLean
