import HeytingLean.Crypto.PCT

namespace Proof2VecQueries

open HeytingLean
open HeytingLean.LoF
open HeytingLean.Crypto

universe u

variable {α : Type u} [HeytingLean.LoF.PrimaryAlgebra α]
variable {R : HeytingLean.LoF.Reentry α}
variable (L : HeytingLean.Crypto.Lens (R := R))

-- In-domain query (this lemma is in the current DB), but the decl is outside `HeytingLean.*`.
theorem q {n : ℕ} (φ : HeytingLean.Crypto.Form n) (ρ : HeytingLean.Crypto.EnvΩ (R := R) n) :
    ∃ payload, HeytingLean.Crypto.Lens.verifies (L := L) payload := by
  simpa using HeytingLean.Crypto.Lens.verifies_complete (L := L) (φ := φ) (ρ := ρ)

end Proof2VecQueries

