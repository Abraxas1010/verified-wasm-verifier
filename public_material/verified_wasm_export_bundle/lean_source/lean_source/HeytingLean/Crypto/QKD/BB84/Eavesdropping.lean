import HeytingLean.Crypto.ConstructiveHardness.Security
import HeytingLean.Crypto.QKD.BB84.Superinfo

/-!
# BB84 eavesdropping strategies (interface-first)

We model eavesdropping strategies at the CT task level using the generic
`EavesdroppingStrategy` interface from `Crypto.ConstructiveHardness.Security`.

At this abstraction layer, the canonical “intercept-resend” attack is modeled as
requiring universal copying (`copyAll`): Eve keeps one copy and forwards one.

This is sufficient to apply the general no-cloning security theorem.
-/

namespace HeytingLean
namespace Crypto
namespace QKD
namespace BB84

open HeytingLean.Constructor.CT
open HeytingLean.Crypto.ConstructiveHardness

/-- Eve's intercept task: clone an arbitrary BB84 state. -/
def eveInterceptTask : CTask BB84Substrate :=
  copyAll

/-- A minimal intercept-resend strategy. -/
def interceptResendStrategy : EavesdroppingStrategy BB84Substrate bb84TaskCT where
  intercept := eveInterceptTask
  gains_info := True
  sound := fun _ => trivial

/-- Intercept-resend requires cloning (trivial in this abstraction: intercept *is* `copyAll`). -/
theorem intercept_resend_requires_copyAll :
    bb84TaskCT.possible interceptResendStrategy.intercept → bb84TaskCT.possible copyAll := by
  intro h
  exact h

end BB84
end QKD
end Crypto
end HeytingLean
