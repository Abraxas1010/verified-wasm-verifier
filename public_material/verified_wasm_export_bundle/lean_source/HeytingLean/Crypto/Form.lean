import Mathlib.Data.Fin.Basic

namespace HeytingLean
namespace Crypto

/-- Intermediate representation for multi-lens programs.
Variables live in a finite context indexed by `Fin n`, giving us a finite
semantic roster while keeping the connectives aligned with the Heyting core. -/
inductive Form (n : ℕ) : Type
  | top
  | bot
  | var (idx : Fin n)
  | and (φ ψ : Form n)
  | or (φ ψ : Form n)
  | imp (φ ψ : Form n)
  deriving DecidableEq, Repr, Inhabited

end Crypto
end HeytingLean
