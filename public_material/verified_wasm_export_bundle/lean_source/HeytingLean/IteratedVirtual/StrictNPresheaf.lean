import Mathlib.CategoryTheory.Yoneda
import HeytingLean.IteratedVirtual.StrictN
import HeytingLean.IteratedVirtual.GlobularToPresheaf
import HeytingLean.IteratedVirtual.NGlobularToGlobularEmpty

/-!
# IteratedVirtual.StrictNPresheaf

Make the slogan “a k-cell is a map `Gₖ → Catₙ`” precise for the **strict** `Catₙ` scaffold:

- interpret a strict `n`-category’s underlying truncated globular data as a full `GlobularSet`
  by making all higher cells empty (`PEmpty`);
- convert that `GlobularSet` to the presheaf presentation `GlobularSetPsh`;
- then a “k-cell” is literally a map from the representable `GlobePsh k`.

This does not claim any weak `Catₙ` semantics; it is a strict-only bridge.
-/

namespace HeytingLean
namespace IteratedVirtual

open CategoryTheory

universe u

namespace StrictNCategory

/-- Underlying presheaf globular set of a strict `n`-category, with empty higher cells. -/
def toPresheaf {n : Nat} (C : StrictNCategory.{u} n) : GlobularSetPsh :=
  (NGlobularSet.toGlobularSetEmpty C.G).toPresheaf

/-- A “top n-cell” in the presheaf sense: a map `GlobePsh n ⟶ C.toPresheaf`. -/
abbrev CellTopPsh {n : Nat} (C : StrictNCategory.{u} n) :=
  kCellPsh (X := C.toPresheaf) n

/-- Package a strict `n`-cell as a globe-map using `uliftYonedaEquiv`. -/
def cellTopPshOf {n : Nat} (C : StrictNCategory.{u} n) (x : C.G.Cell n) : CellTopPsh C := by
  -- Yoneda: maps from the representable `uliftYoneda.obj (ofNat n)` correspond to `n`-cells.
  refine (CategoryTheory.uliftYonedaEquiv (X := GlobularIndex.ofNat n) (F := C.toPresheaf)).symm ?_
  -- Unfold the presheaf conversion; at level `n` this is definitionally the original `n`-cell.
  simpa [StrictNCategory.toPresheaf, GlobularSet.toPresheaf, NGlobularSet.toGlobularSetEmpty]
    using x

end StrictNCategory

end IteratedVirtual
end HeytingLean
