import HeytingLean.Crypto.Form
import HeytingLean.Crypto.Prog
import HeytingLean.Crypto.Lens.Semantics
import HeytingLean.Crypto.VM

namespace HeytingLean
namespace Crypto

open HeytingLean.LoF

universe u v

variable {α : Type u} [PrimaryAlgebra α]
variable {R : Reentry α}

namespace Form

/-- Structural compilation from formulas to postfix programs. -/
def compile : Form n → Program n
  | .top => [.pushTop]
  | .bot => [.pushBot]
  | .var idx => [.pushVar idx]
  | .and φ ψ => compile φ ++ compile ψ ++ [.applyAnd]
  | .or φ ψ => compile φ ++ compile ψ ++ [.applyOr]
  | .imp φ ψ => compile φ ++ compile ψ ++ [.applyImp]

end Form

namespace Lens

variable (L : Lens (R := R))

@[simp] lemma exec_compile_aux {n : ℕ} (ρ : L.EnvL n)
    (φ : Form n) (stk : Stack (L := L)) :
    exec (L := L) ρ (Form.compile φ) stk =
      Form.evalL (L := L) φ ρ :: stk := by
  induction φ generalizing stk with
  | top =>
      simp [Form.compile, Form.evalL, Lens.step]
  | bot =>
      simp [Form.compile, Form.evalL, Lens.step]
  | var idx =>
      simp [Form.compile, Form.evalL, Lens.step]
  | and φ ψ ihφ ihψ =>
      simp [Form.compile, Form.evalL, Lens.exec_append, List.append_assoc,
        ihφ, ihψ, Lens.step, applyBinary_cons_cons]
  | or φ ψ ihφ ihψ =>
      simp [Form.compile, Form.evalL, Lens.exec_append, List.append_assoc,
        ihφ, ihψ, Lens.step, applyBinary_cons_cons]
  | imp φ ψ ihφ ihψ =>
      simp [Form.compile, Form.evalL, Lens.exec_append, List.append_assoc,
        ihφ, ihψ, Lens.step, applyBinary_cons_cons]

lemma exec_compile {n : ℕ} (ρ : L.EnvL n) (φ : Form n) :
    exec (L := L) ρ (Form.compile φ) [] =
      [Form.evalL (L := L) φ ρ] := by
  exact
    exec_compile_aux (L := L) ρ (φ := φ) (stk := [])

lemma run_compile_value {n : ℕ} (ρ : L.EnvL n) (φ : Form n) :
    (run (L := L) (Form.compile φ) ρ).2 =
      Form.evalL (L := L) φ ρ := by
  simp [run, exec_compile (L := L) (ρ := ρ) (φ := φ)]

end Lens

end Crypto
end HeytingLean
