import HeytingLean.Embeddings.PerspectivalDescentCarrier

namespace HeytingLean
namespace Embeddings
namespace GenericLensData

set_option linter.dupNamespace false
/-- Per-tag completion/canonical-subset data, generic over any tag type. -/
structure GenericLensData (τ : Type*) where
  Completion : τ → Type
  Integral : ∀ tag, Set (Completion tag)
  truncate : ∀ tag, Nat → Completion tag → Completion tag

/-- A per-tag precision assignment. -/
abbrev GenericPrecision (τ : Type*) := τ → Nat

/-- Truncation-based approximation for generic tags. -/
def GenericApprox {τ : Type*} (data : GenericLensData τ) (prec : GenericPrecision τ)
    (x y : ∀ t, data.Completion t) : Prop :=
  ∀ tag, data.truncate tag (prec tag) (x tag) = data.truncate tag (prec tag) (y tag)

/-- Explicit projection of finite generic lens-data packages into the PDC interface.
Not an `instance`: `data` is not inferable from `Completion` in general. -/
def toPDC
    {τ : Type*} [Finite τ] (data : GenericLensData τ) :
    PerspectivalDescentCarrier τ data.Completion where
  integral := data.Integral
  finiteness x := by
    simpa using (Set.toFinite {t : τ | x t ∉ data.Integral t})
  truncate := data.truncate

end GenericLensData
end Embeddings
end HeytingLean
