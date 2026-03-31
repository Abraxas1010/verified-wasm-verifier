import Mathlib.Data.Set.Finite.Basic

/-!
# Embeddings.PerspectivalDescentCarrier

Shared interface for perspectival carriers that combine:
- canonical/integral local values,
- adelic-style finite non-integral support,
- finite-precision truncation.
-/

namespace HeytingLean
namespace Embeddings

universe u v

/--
A perspectival descent carrier (PDC) packages the common interface used across
adelic, transport, and descent-oriented families.
-/
class PerspectivalDescentCarrier (τ : Type u) (Carrier : τ → Type v) where
  /-- Canonical/integral values at each perspective. -/
  integral : ∀ t, Set (Carrier t)
  /-- Only finitely many perspectives are non-integral. -/
  finiteness : ∀ (x : ∀ t, Carrier t), {t | x t ∉ integral t}.Finite
  /-- Finite-precision truncation per perspective. -/
  truncate : ∀ t, Nat → Carrier t → Carrier t

namespace PerspectivalDescentCarrier

variable {τ : Type u} {Carrier : τ → Type v} [P : PerspectivalDescentCarrier τ Carrier]

/-- Truncation-based approximation relation induced by a PDC instance. -/
def Approx (prec : τ → Nat) (x y : ∀ t, Carrier t) : Prop :=
  ∀ t, P.truncate t (prec t) (x t) = P.truncate t (prec t) (y t)

end PerspectivalDescentCarrier

end Embeddings
end HeytingLean
