import HeytingLean.Crypto.FHE.Ciphertext
import HeytingLean.Security.Composable.UC

/-!
# UC wiring example: deterministic FHE ciphertext ops

This is a **toy** adapter showing how existing spec-level code can be wrapped into the UC-shaped
interface, without claiming cryptographic security yet.
-/

namespace HeytingLean
namespace Security
namespace Composable
namespace Adapters

open HeytingLean.Crypto.FHE

inductive CiphertextOp where
  | add
  | mul

def CiphertextOpsIF : IdealFunctionality where
  Input := CiphertextOp × Ciphertext × Ciphertext
  Output := Ciphertext
  Leakage := Unit
  compute := fun (op, c₁, c₂) =>
    match op with
    | CiphertextOp.add => (Ciphertext.add c₁ c₂, ())
    | CiphertextOp.mul => (Ciphertext.mul c₁ c₂, ())

def CiphertextOpsProtocol : Protocol CiphertextOpsIF where
  State := Unit
  Message := Unit
  init := ()
  execute := fun i _ =>
    let (o, _leak) := CiphertextOpsIF.compute i
    (o, (), ())

def CiphertextOpsSimulator : Simulator CiphertextOpsIF CiphertextOpsProtocol where
  SimState := Unit
  init := ()
  simulate := fun _ _ => ((), ())

theorem ciphertextOps_uc_secure :
    UCSecure CiphertextOpsIF CiphertextOpsProtocol := by
  refine ⟨CiphertextOpsSimulator, (fun f g => f = g), ?_⟩
  rfl

end Adapters
end Composable
end Security
end HeytingLean
