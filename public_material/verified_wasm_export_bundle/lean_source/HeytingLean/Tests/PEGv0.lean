import HeytingLean.Crypto.Form
import HeytingLean.Crypto.BoolLens
import HeytingLean.Crypto.ZK.R1CS
import HeytingLean.Crypto.ZK.R1CSBool
import HeytingLean.Crypto.ZK.R1CSSoundness
import HeytingLean.Blockchain.Contracts.PEGv0

namespace HeytingLean
namespace Crypto
namespace Tests

open BoolLens
open ZK
open ZK.R1CSBool
open ZK.R1CSSoundness

-- Accept case: all relevant guards true
theorem pegv0_compile_output_eval_allow :
    let φ : Form 5 := HeytingLean.Blockchain.Contracts.PEGv0.permitForm
    let ρ : Env 5 := fun i => match i.1 with
      | 0 => true | 1 => true | 2 => true | 3 => true | 4 => true | _ => false
    boolToRat (BoolLens.eval φ ρ) =
      (compile φ ρ).assignment (compile φ ρ).output := by
  intros; simpa using (compile_output_eval (φ := φ) (ρ := ρ))

@[simp] theorem pegv0_eval_allow_true :
    let φ : Form 5 := HeytingLean.Blockchain.Contracts.PEGv0.permitForm
    let ρ : Env 5 := fun i => match i.1 with
      | 0 => true | 1 => true | 2 => true | 3 => true | 4 => true | _ => false
    BoolLens.eval φ ρ = true := by
  intros; simp [BoolLens.eval, HeytingLean.Blockchain.Contracts.PEGv0.permitForm, ρ]

-- Deny case: whitelist guard (x3) false
theorem pegv0_compile_output_eval_deny :
    let φ : Form 5 := HeytingLean.Blockchain.Contracts.PEGv0.permitForm
    let ρ : Env 5 := fun i => match i.1 with
      | 0 => true | 1 => true | 2 => true | 3 => false | 4 => true | _ => false
    boolToRat (BoolLens.eval φ ρ) =
      (compile φ ρ).assignment (compile φ ρ).output := by
  intros; simpa using (compile_output_eval (φ := φ) (ρ := ρ))

@[simp] theorem pegv0_eval_deny_false :
    let φ : Form 5 := HeytingLean.Blockchain.Contracts.PEGv0.permitForm
    let ρ : Env 5 := fun i => match i.1 with
      | 0 => true | 1 => true | 2 => true | 3 => false | 4 => true | _ => false
    BoolLens.eval φ ρ = false := by
  intros; simp [BoolLens.eval, HeytingLean.Blockchain.Contracts.PEGv0.permitForm, ρ]

end Tests
end Crypto
end HeytingLean

