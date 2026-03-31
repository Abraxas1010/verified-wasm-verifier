import HeytingLean.IteratedVirtual.SpiralStrict22
import HeytingLean.IteratedVirtual.StrictNPresheaf

/-!
# IteratedVirtual.SpiralStrict22Presheaf

Phase‑8 (research-scale) tightening of the slogan “a k-cell is a map `Gₖ → Catₙ`” for the spiral
example:

We expose the 22‑cell data `spiral22Params` as an **actual globe-map** in the presheaf globular
semantics:

`GlobePsh 22 ⟶ spiral22Cat.toPresheaf`.
-/

namespace HeytingLean
namespace IteratedVirtual

open CategoryTheory

namespace SpiralStrict22

/-- The distinguished 22-cell of the spiral example, viewed as an element of the top cell type. -/
def spiral22TopCell : spiral22Cat.G.Cell 22 := by
  simpa [spiral22Cat, spiral22Globular, spiral22CellType] using spiral22Params

/-- The spiral “22-cell” as a globe-map in presheaf globular semantics. -/
def spiral22AsGlobeMap : StrictNCategory.CellTopPsh spiral22Cat :=
  StrictNCategory.cellTopPshOf spiral22Cat spiral22TopCell

end SpiralStrict22

end IteratedVirtual
end HeytingLean

