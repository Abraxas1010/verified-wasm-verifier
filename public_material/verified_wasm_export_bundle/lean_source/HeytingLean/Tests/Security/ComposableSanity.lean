import HeytingLean.Security.Composable.Adapters.FHECiphertext
import HeytingLean.Security.Composable.Adapters.ZKPlonkVerifier
import HeytingLean.Security.Composable.Composition
import HeytingLean.Security.Composable.Instances.IdealKeyExchange
import HeytingLean.Security.Composable.Instances.IdealSecureChannel

/-!
# Test: UC framework sanity

These tests are intentionally small: importing the modules and typechecking a few constructors
exercises the interface-level UC definitions.
-/

namespace HeytingLean.Tests.Security.ComposableSanity

open HeytingLean.Security.Composable

def IdIF (α : Type) : IdealFunctionality where
  Input := α
  Output := α
  Leakage := Unit
  compute := fun a => (a, ())

def IdProtocol (α : Type) : Protocol (IdIF α) where
  State := Unit
  Message := Unit
  init := ()
  execute := fun a _ => (a, (), ())

def IdSim (α : Type) : Simulator (IdIF α) (IdProtocol α) where
  SimState := Unit
  init := ()
  simulate := fun _ _ => ((), ())

theorem id_uc_secure (α : Type) : UCSecure (IdIF α) (IdProtocol α) := by
  refine ⟨IdSim α, (fun f g => f = g), ?_⟩
  rfl

def trivialKit (α : Type) : CompositionKit (IdIF α) (IdIF α) where
  UsesSubroutine := fun _ => True
  compose := fun π₂ _π₁ => π₂
  comp := by
    intro π₁ π₂ h₁ h₂ _hUses
    exact h₂

example (α : Type) :
    UCSecure (IdIF α) ((trivialKit α).compose (IdProtocol α) (IdProtocol α)) :=
  uc_composition (kit := trivialKit α) (h₁ := id_uc_secure α) (h₂ := id_uc_secure α) trivial

example : UCSecure Security.Composable.Adapters.CiphertextOpsIF
    Security.Composable.Adapters.CiphertextOpsProtocol :=
  Security.Composable.Adapters.ciphertextOps_uc_secure

example (P : HeytingLean.Crypto.ZK.Spec.Plonk.Protocol) :
    UCSecure (Security.Composable.Adapters.PlonkVerifierIF P)
      (Security.Composable.Adapters.PlonkVerifierProtocol P) :=
  Security.Composable.Adapters.plonkVerifier_uc_secure P

example : IdealFunctionality :=
  Security.Composable.Instances.IdealKeyExchange 32

example : IdealFunctionality :=
  Security.Composable.Instances.IdealSecureChannel 128

end HeytingLean.Tests.Security.ComposableSanity
