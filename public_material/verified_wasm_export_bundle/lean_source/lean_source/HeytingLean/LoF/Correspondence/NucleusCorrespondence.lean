import Mathlib.Logic.Equiv.Set
import HeytingLean.LoF.Combinators.Heyting.Nucleus
import HeytingLean.LoF.Combinators.Topos.ClosedSievesHeyting

/-!
# NucleusCorrespondence — Grothendieck closure as a LoF-style nucleus

This file is a **bridge layer**: it makes precise that Grothendieck closure on sieves
(`J.close`) is a nucleus in the same `Mathlib.Order.Nucleus` sense used throughout the LoF
development (fixed points, Heyting operations, truncation/kernel quotients).

Concretely, for any Grothendieck topology `J` and object `X`:

* `sieveNucleus J X : Nucleus (Sieve X)` is the closure nucleus;
* its fixed points `Ω_ (sieveNucleus J X)` are exactly the `J`-closed sieves;
* the three standard presentations coincide:
  range of `J.close`  ≃  fixed points of `J.close`  ≃  subtype `J.IsClosed`.
-/

namespace HeytingLean
namespace LoF
namespace Correspondence

open CategoryTheory
open Order

open HeytingLean.LoF.Combinators
open HeytingLean.LoF.Combinators.Heyting
open HeytingLean.LoF.Combinators.Topos

universe v u

variable {C : Type u} [Category.{v} C]

namespace Grothendieck

variable (J : GrothendieckTopology C) (X : C)

/-- Fixed-point presentation of `J`-closed sieves: `Ω_ (sieveNucleus J X)`. -/
abbrev FixedSieve : Type _ :=
  Ω_ (sieveNucleus (C := C) J X)

theorem range_eq_fixedPoints :
    (Set.range (sieveNucleus (C := C) J X)) =
      (Ω_ (sieveNucleus (C := C) J X)) := by
  ext S
  -- `Nucleus.mem_range` says: `S ∈ range n ↔ n S = S`.
  -- `Ω_ n` is defined by the same predicate.
  simpa [HeytingLean.LoF.Combinators.Heyting.mem_fixedPoints_iff] using
    (Nucleus.mem_range (n := sieveNucleus (C := C) J X) (x := S))

/-- Range-of-closure and fixed-point presentations are equivalent (for a nucleus, they coincide). -/
noncomputable def closedSieveEquivFixedSieve :
    ClosedSieve (C := C) J X ≃ FixedSieve (C := C) J X :=
  Equiv.setCongr (range_eq_fixedPoints (C := C) (J := J) X)

/-- Fixed points of the sieve nucleus are exactly the `J.IsClosed` sieves. -/
noncomputable def fixedSieveEquivIsClosed :
    FixedSieve (C := C) J X ≃ IsClosedSieve (C := C) J X := by
  classical
  refine
    { toFun := fun S => ?_
      invFun := fun S => ?_
      left_inv := ?_
      right_inv := ?_ }
  · refine ⟨S.1, ?_⟩
    exact (mem_fixedPoints_sieveNucleus_iff_isClosed (C := C) J (X := X) S.1).1 S.2
  · refine ⟨S.1, ?_⟩
    exact (mem_fixedPoints_sieveNucleus_iff_isClosed (C := C) J (X := X) S.1).2 S.2
  · intro S
    ext
    rfl
  · intro S
    ext
    rfl

/-- All three presentations of closed sieves line up. -/
noncomputable def closedSieveEquivIsClosed_viaFixed :
    ClosedSieve (C := C) J X ≃ IsClosedSieve (C := C) J X :=
  (closedSieveEquivFixedSieve (C := C) (J := J) X).trans
    (fixedSieveEquivIsClosed (C := C) (J := J) X)

end Grothendieck

end Correspondence
end LoF
end HeytingLean

