import HeytingLean.CDL.Coalgebra.Mealy
import HeytingLean.ClosingTheLoop.Semantics.Mealy

/-!
# CDL ↔ ClosingTheLoop: Mealy bridge

The ClosingTheLoop layer already defines a minimal deterministic Mealy machine
`HeytingLean.ClosingTheLoop.Semantics.Mealy` with step function `S → I → S × O`.

This file provides lossless conversions between that definition and the CDL-layer
parametric coalgebra `HeytingLean.CDL.Coalgebra.ParaMealy`:

- ordinary Mealy machines embed as trivially-parametric (`P := PUnit`),
- fixing parameters of a `ParaMealy` yields an ordinary Mealy machine.
-/

namespace HeytingLean
namespace CDL
namespace Coalgebra

open HeytingLean.ClosingTheLoop
open HeytingLean.ClosingTheLoop.Semantics

universe u

namespace ParaMealy

variable {I O S : Type u}

/-- Embed an ordinary ClosingTheLoop Mealy machine as a trivially-parametric `ParaMealy`. -/
def ofClosingMealy (m : Semantics.Mealy I O S) : ParaMealy I O S where
  P := PUnit
  transition := fun
    | (⟨⟩, i, s) => m.step s i

@[simp] theorem ofClosingMealy_P (m : Semantics.Mealy I O S) :
    (ofClosingMealy (I := I) (O := O) (S := S) m).P = PUnit := rfl

/-- Fixing parameters of a `ParaMealy` yields an ordinary ClosingTheLoop Mealy machine. -/
def toClosingMealy (m : ParaMealy I O S) (p : m.P) : Semantics.Mealy I O S where
  step := fun s i => m.transition (p, i, s)

@[simp] theorem toClosingMealy_step (m : ParaMealy I O S) (p : m.P) (s : S) (i : I) :
    (toClosingMealy (I := I) (O := O) (S := S) m p).step s i = m.transition (p, i, s) := rfl

end ParaMealy

end Coalgebra
end CDL
end HeytingLean

