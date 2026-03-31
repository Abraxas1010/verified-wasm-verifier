import HeytingLean.Crypto.PCT

namespace Proof2VecQueries

open HeytingLean
open HeytingLean.LoF
open HeytingLean.Crypto

universe u

variable {α : Type u} [HeytingLean.LoF.PrimaryAlgebra α]
variable {R : HeytingLean.LoF.Reentry α}
variable (L : HeytingLean.Crypto.Lens (R := R))

-- In-domain query: expects neighbors around the canonical payload verification lemma.
theorem q {n : ℕ} (φ : HeytingLean.Crypto.Form n) (ρ : HeytingLean.Crypto.EnvΩ (R := R) n) :
    HeytingLean.Crypto.Lens.verifies (L := L)
      (HeytingLean.Crypto.Lens.canonicalPayload (L := L) (φ := φ) (ρ := ρ)) := by
  simpa using HeytingLean.Crypto.Lens.canonicalPayload_verifies (L := L) (φ := φ) (ρ := ρ)

end Proof2VecQueries

