import Mathlib.CategoryTheory.Types.Basic
import HeytingLean.IteratedVirtual.Examples.CobordismCells

/-!
# Tests.IteratedVirtual.CobordismCellSanity

Smoke test: build a concrete `CobordismOver` and ensure `cobordismAsSquareCell` elaborates.
-/

namespace HeytingLean
namespace Tests
namespace IteratedVirtual

open CategoryTheory

def cobordismAsCell_elaborates : True := by
  let A : HeytingLean.IteratedVirtual.IteratedCellOver (C := Type) PUnit PUnit 1 :=
    HeytingLean.IteratedVirtual.IteratedCellOver.ofHom (C := Type) (fun _ => PUnit.unit)
  let T : HeytingLean.IteratedVirtual.CobordismOver (C := Type) A A :=
    HeytingLean.IteratedVirtual.CobordismOver.refl (C := Type) A
  let _cell :=
    HeytingLean.IteratedVirtual.Examples.cobordismAsSquareCell (C := Type) (A := A) (B := A) T
  trivial

end IteratedVirtual
end Tests
end HeytingLean
