import Mathlib.Tactic
import HeytingLean.LoF.MRSystems.Coalgebra

/-!
Sanity checks for `LoF/MRSystems/Coalgebra.lean`.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.LoF.MRSystems

-- The reader endofunctor is well-typed.
#check ReaderEndo

-- A tiny toy (M,R) core where `R` ignores the input and returns the current state.
private def toy : MRCore :=
  { A := Bool
    B := Bool
    M := id
    R := fun b => fun _a => b }

-- Uniform closure holds for the toy system.
example : toy.ClosedAll := by
  intro a a'
  cases a <;> cases a' <;> rfl

-- Hence diagonal closure holds.
example : toy.ClosedDiag := (MRCore.ClosedAll.closedDiag (m := toy) (by
  intro a a'
  cases a <;> cases a' <;> rfl))

-- Closure is equivalently a fixed-point condition.
example : (toy.ClosedDiag ↔ ∀ a : toy.A, Function.IsFixedPt (fun b : toy.B => toy.R b a) (toy.M a)) :=
  toy.closedDiag_iff_isFixedPt

-- `R` packages as a `Coalgebra` for the reader endofunctor.
#check (MRCore.toCoalgebra toy)

end LoF
end Tests
end HeytingLean

