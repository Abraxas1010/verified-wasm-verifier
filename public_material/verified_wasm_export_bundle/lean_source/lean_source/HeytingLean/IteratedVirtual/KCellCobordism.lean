import HeytingLean.IteratedVirtual.VirtualComposition
import HeytingLean.IteratedVirtual.Globe

/-!
# IteratedVirtual.KCellCobordism

Cobordisms and their “virtual compositions” between **globular** k-cells.

Key point: since `GlobularSet` is a `Category` (see `IteratedVirtual.Globular`), a k-cell
`A : Globe k ⟶ X` is literally a morphism, so we can reuse:
- `CobordismHom` for cobordisms between parallel morphisms, and
- `VirtualCobordismHom` for chains (“virtual compositions”) of cobordisms.
-/

namespace HeytingLean
namespace IteratedVirtual

open GlobularSet

universe u

abbrev KCellCobordism (X : GlobularSet.{u}) (k : Nat) (A B : kCell (X := X) k) :=
  CobordismHom (C := GlobularSet.{u}) A B

abbrev KCellVirtualCobordism (X : GlobularSet.{u}) (k : Nat) (A B : kCell (X := X) k) :=
  VirtualCobordismHom (C := GlobularSet.{u}) A B

end IteratedVirtual
end HeytingLean
