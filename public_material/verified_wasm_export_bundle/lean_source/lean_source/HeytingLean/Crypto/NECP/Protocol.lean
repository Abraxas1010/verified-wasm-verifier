import HeytingLean.Crypto.NECP.LinearClosure
import HeytingLean.Crypto.NECP.NRAExperiment

namespace HeytingLean
namespace Crypto
namespace NECP

section

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- Minimal NECP protocol surface: the operator defines the observable closure published to the
adversary, and guesses are judged by equality of their published closures. -/
structure NECPProtocol where
  operator : M →ₗ[R] M

namespace NECPProtocol

variable (P : NECPProtocol (R := R) (M := M))

/-- Public observation exposed by the protocol. -/
def publish (secret : Submodule R M) : Submodule R M :=
  linearClosure P.operator secret

/-- Verification accepts when the guess induces the same public closure as the secret. -/
def verifies (guess secret : Submodule R M) : Prop :=
  P.publish guess = P.publish secret

theorem verifies_refl (secret : Submodule R M) :
    P.verifies secret secret := rfl

theorem publish_contains_range (secret : Submodule R M) :
    LinearMap.range P.operator ≤ P.publish secret := by
  exact le_sup_right

theorem publish_idempotent (secret : Submodule R M) :
    P.publish (P.publish secret) = P.publish secret :=
  linearClosure_idempotent P.operator secret

/-- The protocol induces an abstract NRA experiment on submodules. -/
def toNRAExperiment : NRAExperiment (Submodule R M) (Submodule R M) (Submodule R M) where
  encode := P.publish
  solvedBy guess secret := P.verifies guess secret

end NECPProtocol

end

end NECP
end Crypto
end HeytingLean
