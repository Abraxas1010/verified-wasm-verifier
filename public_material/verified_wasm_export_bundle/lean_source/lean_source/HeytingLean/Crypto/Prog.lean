import Mathlib.Data.Fin.Basic

namespace HeytingLean
namespace Crypto

/-- Postfix instructions for the multi-lens VM. -/
inductive Instr (n : ℕ)
  | pushTop
  | pushBot
  | pushVar (idx : Fin n)
  | applyAnd
  | applyOr
  | applyImp
  deriving DecidableEq, Repr, Inhabited

/-- Programs are finite sequences of instructions. -/
abbrev Program (n : ℕ) := List (Instr n)

end Crypto
end HeytingLean
