import HeytingLean.Crypto.Form
import HeytingLean.Crypto.BoolLens
import HeytingLean.Crypto.ZK.R1CS
import HeytingLean.Crypto.ZK.R1CSBool
import HeytingLean.Crypto.ZK.R1CSSoundness

namespace HeytingLean
namespace Crypto
namespace Tests

open BoolLens
open ZK
open ZK.R1CSBool
open ZK.R1CSSoundness

-- Two quick proof-side checks of the compiled Boolean R1CS.

theorem pct_compile_output_eval_example1 :
    let n := 2
    let φ : Form n :=
      Form.and (.var ⟨0, by decide⟩)
               (Form.or (.var ⟨1, by decide⟩)
                        (Form.imp (.var ⟨0, by decide⟩) (.var ⟨1, by decide⟩)))
    let ρ : Env n := fun i => match i.1 with | 0 => true | _ => false
    boolToRat (BoolLens.eval φ ρ) =
      (compile φ ρ).assignment (compile φ ρ).output := by
  intros; simpa using (compile_output_eval (φ := φ) (ρ := ρ))

theorem pct_compile_satisfied_example2 :
    let n := 1
    let φ : Form n := Form.var ⟨0, by decide⟩
    let ρ : Env n := fun _ => false
    System.satisfied (compile φ ρ).assignment (compile φ ρ).system := by
  intros; exact compile_satisfied (φ := φ) (ρ := ρ)

end Tests
end Crypto
end HeytingLean

