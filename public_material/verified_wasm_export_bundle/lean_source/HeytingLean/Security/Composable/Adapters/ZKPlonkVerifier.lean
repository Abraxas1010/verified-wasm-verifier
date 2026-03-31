import HeytingLean.Crypto.ZK.Spec.Plonk
import HeytingLean.Security.Composable.UC

/-!
# UC wiring example: PLONK verifier as an ideal functionality

This is a minimal adapter showing how an existing ZK spec interface can be wrapped into the
UC-shaped interface. It is **not** a UC-security proof of PLONK; it is only a sanity-level
real/ideal equivalence for a deterministic verifier experiment.
-/

namespace HeytingLean
namespace Security
namespace Composable
namespace Adapters

open HeytingLean.Crypto.ZK.Spec

def PlonkVerifierIF (P : Plonk.Protocol) : IdealFunctionality where
  Input := P.Public × P.Proof
  Output := Bool
  Leakage := Unit
  compute := fun (pub, π) => (P.verify pub π, ())

def PlonkVerifierProtocol (P : Plonk.Protocol) : Protocol (PlonkVerifierIF P) where
  State := Unit
  Message := Unit
  init := ()
  execute := fun (pub, π) _ => (P.verify pub π, (), ())

def PlonkVerifierSimulator (P : Plonk.Protocol) :
    Simulator (PlonkVerifierIF P) (PlonkVerifierProtocol P) where
  SimState := Unit
  init := ()
  simulate := fun _ _ => ((), ())

theorem plonkVerifier_uc_secure (P : Plonk.Protocol) :
    UCSecure (PlonkVerifierIF P) (PlonkVerifierProtocol P) := by
  refine ⟨PlonkVerifierSimulator P, (fun f g => f = g), ?_⟩
  rfl

end Adapters
end Composable
end Security
end HeytingLean
