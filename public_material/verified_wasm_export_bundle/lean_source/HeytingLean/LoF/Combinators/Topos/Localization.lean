import HeytingLean.LoF.Combinators.Topos.ClosedSievesHeyting
import HeytingLean.LoF.Combinators.Topos.NucleusFunctor

/-!
# Localization — closed sieves as a reflective subframe

For a Grothendieck topology `J`, the closure operation `J.close` is a nucleus on the frame
`Sieve X`. The *range* (equivalently, the fixed points) of a nucleus is a reflective subframe.

This file packages that pattern for the sieve nucleus `sieveNucleus J X`.
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

variable (J : GrothendieckTopology C) (X : C)

noncomputable def closeRestrict : FrameHom (Sieve X) (ClosedSieve (C := C) J X) :=
  (sieveNucleus (C := C) J X).restrict

@[simp] theorem closeRestrict_val (S : Sieve X) :
    (closeRestrict (C := C) J X S : Sieve X) = J.close S := rfl

/-- The reflector/inclusion adjunction, expressed as a Galois insertion on the underlying orders. -/
noncomputable def closeGI : GaloisInsertion (closeRestrict (C := C) J X) Subtype.val :=
  (sieveNucleus (C := C) J X).giRestrict

/-- Universal property of `J.close` phrased via the restricted map into `ClosedSieve`. -/
theorem closeRestrict_le_iff {S : Sieve X} {T : ClosedSieve (C := C) J X} :
    closeRestrict (C := C) J X S ≤ T ↔ S ≤ (T : Sieve X) := by
  simpa [closeRestrict] using ((sieveNucleus (C := C) J X).giRestrict).gc S T

end

end Topos
end Combinators
end LoF
end HeytingLean

