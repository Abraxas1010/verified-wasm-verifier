import HeytingLean.Crypto.ConstructiveHardness.VirtualRequiresChain
import HeytingLean.Crypto.QKD.BB84.Eavesdropping

/-!
# Tests.Crypto.VirtualRequiresChainSanity

Compile-only checks that CT “requires” implications can be tracked as a `VirtualChain`.
-/

namespace HeytingLean.Tests.Crypto

open HeytingLean.Crypto.ConstructiveHardness
open HeytingLean.Crypto.QKD.BB84
open HeytingLean.Constructor.CT
open HeytingLean.Crypto.ConstructiveHardness.RequiresChain

-- A 1-step chain: intercept-resend intercept requires `copyAll`.
def bb84_intercept_requires_copyAll_chain :
    RequiresChain.Chain bb84TaskCT
      interceptResendStrategy.intercept copyAll :=
  HeytingLean.Util.VirtualChain.cons (Step := RequiresChain.Step bb84TaskCT)
    (a := interceptResendStrategy.intercept)
    (b := copyAll)
    (c := copyAll)
    intercept_resend_requires_copyAll
    (HeytingLean.Util.VirtualChain.nil (Step := RequiresChain.Step bb84TaskCT) copyAll)

-- Security transfer via the chain (same logical content as `ConstructiveHardness.composed_security`,
-- but with explicit provenance as a chain).
example : bb84TaskCT.impossible interceptResendStrategy.intercept :=
  RequiresChain.composed_security (CT := bb84TaskCT)
    bb84_intercept_requires_copyAll_chain
    copyAll_impossible

end HeytingLean.Tests.Crypto
