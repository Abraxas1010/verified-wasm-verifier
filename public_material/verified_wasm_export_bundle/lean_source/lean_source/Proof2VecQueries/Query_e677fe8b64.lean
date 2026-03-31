import HeytingLean.Crypto.PCT

namespace Proof2VecQueries

open HeytingLean
open HeytingLean.LoF
open HeytingLean.Crypto

universe u

variable {α : Type u} [HeytingLean.LoF.PrimaryAlgebra α]
variable {R : HeytingLean.LoF.Reentry α}
variable (L : HeytingLean.Crypto.Lens (R := R))

-- In-domain query: expects neighbors around the PCT Lens soundness lemma.
theorem q {n : ℕ} (φ : HeytingLean.Crypto.Form n) (ρ : HeytingLean.Crypto.EnvΩ (R := R) n)
    (payload : HeytingLean.Crypto.Lens.Payload (L := L))
    (h : HeytingLean.Crypto.Lens.verifies (L := L) payload) :
    L.dec (HeytingLean.Crypto.Lens.canonicalValue (L := L) (φ := payload.form) (ρ := payload.env)) =
      HeytingLean.Crypto.Form.evalΩ (R := R) payload.form payload.env := by
  simpa using HeytingLean.Crypto.Lens.verifies_sound (L := L) (payload := payload) h

end Proof2VecQueries
