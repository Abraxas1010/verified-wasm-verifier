import Mathlib.Order.Closure
import HeytingLean.LoF.Comparison.Functors
import HeytingLean.LoF.Comparison.Proofs

/-!
Comparison nucleus (act only)

We expose the comparison act Rc := g ∘ f from a Spec. Packaging as a full
`Order.Nucleus` requires meet preservation in equality form; since we keep this
module generic, we export the act and its basic facts (monotone, extensive,
idempotent). Downstream code can select this act via a single selector.
-/

namespace HeytingLean
namespace LoF
namespace Comparison

open Classical

universe u v

def act {L : Type u} {Ωℓ : Type v} (S : Spec L Ωℓ) : L → L := Rc S

lemma act_monotone {L : Type u} {Ωℓ : Type v} (S : Spec L Ωℓ) : Monotone (act S) := Rc_monotone S
lemma act_extensive {L : Type u} {Ωℓ : Type v} (S : Spec L Ωℓ) : ∀ x, x ≤ act S x := Rc_extensive S
lemma act_idempotent {L : Type u} {Ωℓ : Type v} (S : Spec L Ωℓ) : ∀ x, act S (act S x) = act S x := Rc_idempotent S

end Comparison
end LoF
end HeytingLean
