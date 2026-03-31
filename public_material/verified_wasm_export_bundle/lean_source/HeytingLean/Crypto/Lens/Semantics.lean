import HeytingLean.Crypto.Form
import HeytingLean.Crypto.Lens.Class

namespace HeytingLean
namespace Crypto

open HeytingLean.LoF

universe u v

variable {α : Type u} [PrimaryAlgebra α]
variable {R : Reentry α}

namespace Lens

variable (L : Lens (R := R))

/-- Lens-side environments over a finite roster. -/
abbrev EnvL (n : ℕ) := Fin n → L.Carrier

namespace Form

variable {n : ℕ}

/-- Evaluate a `Form` using the operations induced by a given lens. -/
def evalL (L : Lens (R := R)) :
    Form n → L.EnvL n → L.Carrier
  | .top, _ => L.top
  | .bot, _ => L.bot
  | .var idx, ρ => ρ idx
  | .and φ ψ, ρ =>
      L.and (evalL (L := L) φ ρ) (evalL (L := L) ψ ρ)
  | .or φ ψ, ρ =>
      L.or (evalL (L := L) φ ρ) (evalL (L := L) ψ ρ)
  | .imp φ ψ, ρ =>
      L.imp (evalL (L := L) φ ρ) (evalL (L := L) ψ ρ)

variable {L}

@[simp] lemma evalL_top (ρ : L.EnvL n) :
    evalL (L := L) (Form.top : Form n) ρ = L.top := rfl

@[simp] lemma evalL_bot (ρ : L.EnvL n) :
    evalL (L := L) (Form.bot : Form n) ρ = L.bot := rfl

@[simp] lemma evalL_var (ρ : L.EnvL n) (i : Fin n) :
    evalL (L := L) (.var i) ρ = ρ i := rfl

@[simp] lemma evalL_and (ρ : L.EnvL n) (φ ψ : Form n) :
    evalL (L := L) (.and φ ψ) ρ =
      L.and (evalL (L := L) φ ρ) (evalL (L := L) ψ ρ) := rfl

@[simp] lemma evalL_or (ρ : L.EnvL n) (φ ψ : Form n) :
    evalL (L := L) (.or φ ψ) ρ =
      L.or (evalL (L := L) φ ρ) (evalL (L := L) ψ ρ) := rfl

@[simp] lemma evalL_imp (ρ : L.EnvL n) (φ ψ : Form n) :
    evalL (L := L) (.imp φ ψ) ρ =
      L.imp (evalL (L := L) φ ρ) (evalL (L := L) ψ ρ) := rfl

end Form

end Lens

end Crypto
end HeytingLean
