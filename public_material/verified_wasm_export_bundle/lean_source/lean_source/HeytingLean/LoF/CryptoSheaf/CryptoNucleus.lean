import HeytingLean.LoF.Nucleus
import HeytingLean.LoF.HeytingCore

/-
CryptoSheaf/CryptoNucleus

Lightweight alias exposing the LoF reentry nucleus as a crypto nucleus.
This keeps the API close to the homomorphic/ZK modules.
-/

namespace HeytingLean
namespace LoF
namespace CryptoSheaf

open HeytingLean.LoF

variable {α : Type u} [PrimaryAlgebra α]

/-- A crypto nucleus is just the standard LoF reentry nucleus. -/
abbrev CryptoNucleus (α : Type u) [PrimaryAlgebra α] := Reentry α

namespace CryptoNucleus

variable (R : Reentry α)

/-- Encrypt an ambient element as a fixed point. -/
def encrypt (a : α) : R.Omega :=
  Reentry.Omega.mk (R := R) (R a) (R.idempotent a)

/-- Decrypt is the underlying element. -/
def decrypt (aΩ : R.Omega) : α := (aΩ : α)

@[simp] lemma decrypt_encrypt (a : α) : decrypt (R := R) (encrypt (R := R) a) = R a := rfl

end CryptoNucleus

end CryptoSheaf
end LoF
end HeytingLean

