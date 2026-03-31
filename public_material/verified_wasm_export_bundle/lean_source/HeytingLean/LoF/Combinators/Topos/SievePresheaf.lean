import Mathlib.CategoryTheory.Sites.Closed

/-!
# SievePresheaf — the presheaf of sieves and closure as a natural transformation

Phase C needs a precise answer to: “how does `J.close` act on morphisms?”

The mathematically correct statement is that Grothendieck closure commutes with pullback:

`J.close (S.pullback f) = (J.close S).pullback f`.

Equivalently, `J.close` is a natural transformation of the presheaf `X ↦ Sieve X`.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Topos

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

/-- The presheaf of sieves: `X ↦ Sieve X`. -/
def sievePresheaf : Cᵒᵖ ⥤ Type max v u where
  obj X := Sieve X.unop
  map {X Y} f S := S.pullback f.unop
  map_id := by
    intro X
    ext Y f
    simp
  map_comp := by
    intro X Y Z f g
    ext W h
    simp

/-- Grothendieck closure as a natural transformation of the sieve presheaf. -/
def closeNatTrans (J : GrothendieckTopology C) : sievePresheaf (C := C) ⟶ sievePresheaf (C := C) where
  app X S := J.close S
  naturality {X Y} f := by
    funext S
    -- `pullback_close` is exactly the naturality square.
    simpa using (J.pullback_close (f := f.unop) (S := S))

end Topos
end Combinators
end LoF
end HeytingLean
