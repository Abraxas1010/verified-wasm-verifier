import HeytingLean.Coalgebra.Universal.Core

/-!
# Universal coalgebra (Type) — quotients (limited)

This file provides a *minimal* quotient construction for `Type`-coalgebras.

Given a coalgebra `S : Coalg F` and a setoid `≈` on `S.V`, we can form a coalgebra on the
quotient `Quotient (Setoid.mk ..)` provided the structure map respects the quotient in the
following strong sense:

`s ≈ t → F.map (Quotient.mk _) (S.str s) = F.map (Quotient.mk _) (S.str t)`.

This is sufficient to build an induced coalgebra structure and show the quotient map is a
coalgebra homomorphism.

Note: this is not yet specialized to “quotient by bisimilarity”; that requires additional work
to show the bisimilarity relation is compatible with the structure map in the equality sense
above (often via a relator).
-/

namespace HeytingLean
namespace Coalgebra
namespace Universal

open CategoryTheory

universe u

variable {F : Type u ⥤ Type u}

namespace Quotients

variable (S : Universal.Coalg (F := F))
variable (r : Setoid S.V)

abbrev Q := Quotient r

/-- Compatibility condition needed to define the induced quotient coalgebra structure. -/
def Compatible : Prop :=
  ∀ ⦃s t : S.V⦄, r.r s t →
    F.map (Quotient.mk r) (S.str s) = F.map (Quotient.mk r) (S.str t)

/-- Induced coalgebra on the quotient, given the compatibility condition. -/
def quotientCoalg (h : Compatible (F := F) S r) : Universal.Coalg (F := F) :=
  Universal.Coalg.mk (F := F) (Q (S := S) r) (fun q =>
    Quotient.liftOn q
      (fun s => F.map (Quotient.mk r) (S.str s))
      (by
        intro a b hab
        exact h hab))

/-- The quotient map is a coalgebra homomorphism. -/
def quotientHom (h : Compatible (F := F) S r) : S ⟶ quotientCoalg (F := F) S r h where
  f := Quotient.mk r
  h := by
    -- In `Type`, this is pointwise extensionality.
    funext s
    rfl

end Quotients

end Universal
end Coalgebra
end HeytingLean
