import HeytingLean.LoF.IntReentry

/-!
# Round-trip contracts (interior variant)

Interior-nucleus analogue of the round-trip interface. This mirrors the
`Contracts.RoundTrip` API but for `IntReentry` cores (interior operators).
It is intentionally minimal (encode/decode/round), suitable for lenses
whose native stabilizer is an interior operator (e.g., topological interior).
-/

namespace HeytingLean
namespace Contracts

open HeytingLean.LoF

variable {α : Type u} [PrimaryAlgebra α]

/-- A round-trip contract for an interior nucleus core. -/
structure IntRoundTrip (R : IntReentry α) (β : Type v) where
  encode : R.Omega → β
  decode : β → R.Omega
  round : ∀ a, decode (encode a) = a

/-- Interiorized representative for the interior variant, obtained by decoding
    and viewing the core element back in the ambient carrier. -/
def interiorizedInt (R : IntReentry α) {β : Type v}
    (C : IntRoundTrip (R := R) β) : β → α :=
  fun b => ((C.decode b : R.Omega) : α)

@[simp] lemma interiorizedInt_id (R : IntReentry α) {β}
    (C : IntRoundTrip (R := R) β) (a) :
    interiorizedInt (R := R) C (C.encode a) = (a : α) := by
  unfold interiorizedInt
  simpa using congrArg (fun x : R.Omega => (x : α)) (C.round a)

end Contracts
end HeytingLean
