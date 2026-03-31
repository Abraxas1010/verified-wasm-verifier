import HeytingLean.Crypto.ConstructiveHardness.Composition
import HeytingLean.Crypto.ConstructiveHardness.Security
import HeytingLean.Crypto.QKD.BB84.Eavesdropping

/-!
# BB84 security (Constructor-Theoretic)

This file applies the general theorem
`HeytingLean.Crypto.ConstructiveHardness.superinfo_secure_against_eavesdropping`
to the BB84 superinformation medium instance.
-/

namespace HeytingLean
namespace Crypto
namespace QKD
namespace BB84

open HeytingLean.Constructor.CT
open HeytingLean.Crypto.ConstructiveHardness

/-- BB84 is secure against eavesdropping (in the CT sense). -/
theorem bb84_secure : SecureAgainstEavesdropping BB84Substrate bb84TaskCT bb84Superinfo :=
  superinfo_secure_against_eavesdropping bb84TaskCT bb84Superinfo

/-- Explicit statement: intercept-resend is CT-impossible. -/
theorem intercept_resend_impossible :
    bb84TaskCT.impossible interceptResendStrategy.intercept := by
  have hsec : SecureAgainstEavesdropping BB84Substrate bb84TaskCT bb84Superinfo := bb84_secure
  refine hsec interceptResendStrategy ?_
  intro hPossible
  -- `bb84Superinfo.copyXY` is definitionally `copyAll`.
  simpa [bb84Superinfo] using (intercept_resend_requires_copyAll hPossible)

/-- If a multi-round BB84 attack requires single-round cloning as a subtask, it is also impossible. -/
theorem bb84_composed_security
    {T_attack : CTask BB84Substrate}
    (h_requires : bb84TaskCT.possible T_attack → bb84TaskCT.possible copyAll) :
    bb84TaskCT.impossible T_attack :=
  composed_security h_requires copyAll_impossible

end BB84
end QKD
end Crypto
end HeytingLean
