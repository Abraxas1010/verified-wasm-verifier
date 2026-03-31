import HeytingLean.LoF.HeytingCore
import HeytingLean.Crypto.Form

namespace HeytingLean
namespace Crypto

open HeytingLean.LoF

universe u

variable {α : Type u} [PrimaryAlgebra α]

/-- Environments for core evaluation: a finite roster of fixed-point values. -/
abbrev EnvΩ (R : Reentry α) (n : ℕ) :=
  Fin n → R.Omega

namespace Form

variable {R : Reentry α}

/-- Evaluate a `Form` inside the Heyting core `Ω_R`. -/
def evalΩ {n : ℕ} (R : Reentry α) :
    Form n → EnvΩ (R := R) n → R.Omega
  | .top => fun _ => ⊤
  | .bot => fun _ => ⊥
  | .var idx => fun ρ => ρ idx
  | .and φ ψ => fun ρ =>
      evalΩ (R := R) φ ρ ⊓ evalΩ (R := R) ψ ρ
  | .or φ ψ => fun ρ =>
      evalΩ (R := R) φ ρ ⊔ evalΩ (R := R) ψ ρ
  | .imp φ ψ => fun ρ =>
      evalΩ (R := R) φ ρ ⇨ evalΩ (R := R) ψ ρ

variable {n : ℕ} (R) (φ ψ : Form n) (ρ : EnvΩ (R := R) n)

@[simp] lemma evalΩ_top : evalΩ (R := R) Form.top ρ = (⊤ : R.Omega) := rfl

@[simp] lemma evalΩ_bot : evalΩ (R := R) Form.bot ρ = (⊥ : R.Omega) := rfl

@[simp] lemma evalΩ_var (i : Fin n) :
    evalΩ (R := R) (Form.var i) ρ = ρ i := rfl

@[simp] lemma evalΩ_and :
    evalΩ (R := R) (Form.and φ ψ) ρ =
      evalΩ (R := R) φ ρ ⊓ evalΩ (R := R) ψ ρ := rfl

@[simp] lemma evalΩ_or :
    evalΩ (R := R) (Form.or φ ψ) ρ =
      evalΩ (R := R) φ ρ ⊔ evalΩ (R := R) ψ ρ := rfl

@[simp] lemma evalΩ_imp :
    evalΩ (R := R) (Form.imp φ ψ) ρ =
      evalΩ (R := R) φ ρ ⇨ evalΩ (R := R) ψ ρ := rfl

end Form

end Crypto
end HeytingLean
