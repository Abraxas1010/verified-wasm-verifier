import HeytingLean.Crypto.Security.Game

namespace HeytingLean
namespace Crypto
namespace Security

/-- Shared distinguishing-advantage surface for two challenge branches. -/
structure Advantage where
  challenge0 : Nat
  challenge1 : Nat
  deriving Repr, DecidableEq

/-- Absolute gap between the two challenge branches. -/
def Advantage.gap (adv : Advantage) : Nat :=
  if adv.challenge0 ≤ adv.challenge1 then
    adv.challenge1 - adv.challenge0
  else
    adv.challenge0 - adv.challenge1

theorem Advantage.gap_nonneg (adv : Advantage) : 0 ≤ adv.gap := by
  exact Nat.zero_le _

end Security
end Crypto
end HeytingLean
