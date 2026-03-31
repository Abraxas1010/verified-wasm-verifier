import HeytingLean.LoF.Combinators.Topos.SieveNucleus

/-!
# NucleusFunctor — nucleus-like laws for `J.close`

This file collects a small API around Grothendieck closure on sieves (`J.close`) in the style
used by the SKY–Heyting–∞ program.

The key point is that `J.close` behaves like a *nucleus* on the frame `Sieve X`:
it is inflationary, idempotent, and preserves finite meets, and it is stable under pullback.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Topos

open CategoryTheory
open Order

universe v u

variable {C : Type u} [Category.{v} C]

section

variable (J : GrothendieckTopology C)
variable {X Y : C}

theorem monotone_close {X : C} : Monotone (J.close : Sieve X → Sieve X) :=
  J.monotone_close

@[simp] theorem close_close {X : C} (S : Sieve X) : J.close (J.close S) = J.close S :=
  J.close_close S

theorem close_isClosed {X : C} (S : Sieve X) : J.IsClosed (J.close S) :=
  J.close_isClosed S

theorem close_eq_self_of_isClosed {X : C} {S : Sieve X} (hS : J.IsClosed S) : J.close S = S :=
  J.close_eq_self_of_isClosed hS

/-- Universal property: for a closed sieve `T`, we have `J.close S ≤ T ↔ S ≤ T`. -/
theorem close_le_iff_of_isClosed {X : C} {S T : Sieve X} (hT : J.IsClosed T) :
    J.close S ≤ T ↔ S ≤ T := by
  constructor
  · intro h
    exact le_trans (J.le_close S) h
  · intro h
    exact J.le_close_of_isClosed h hT

/-- Closing is stable under pullback. -/
theorem pullback_close {X Y : C} (f : Y ⟶ X) (S : Sieve X) :
    J.close (S.pullback f) = (J.close S).pullback f :=
  J.pullback_close f S

end

@[simp] theorem sieveNucleus_apply (J : GrothendieckTopology C) (X : C) (S : Sieve X) :
    sieveNucleus (C := C) J X S = J.close S := rfl

/--
Queue anchor theorem for `ontology_reentry_grothendieck_closure_20260219`:
fixed points of the Grothendieck sieve nucleus are exactly closed sieves.
-/
@[simp] theorem ontology_reentry_grothendieck_closure_20260219
    (J : GrothendieckTopology C) {X : C} (S : Sieve X) :
    S ∈ HeytingLean.LoF.Combinators.Heyting.FixedPoints (sieveNucleus (C := C) J X) ↔ J.IsClosed S :=
  mem_fixedPoints_sieveNucleus_iff_isClosed (J := J) (S := S)

end Topos
end Combinators
end LoF
end HeytingLean
