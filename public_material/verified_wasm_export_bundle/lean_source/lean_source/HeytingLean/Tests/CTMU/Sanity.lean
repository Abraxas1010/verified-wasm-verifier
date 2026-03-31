import HeytingLean.CTMU.Core
import HeytingLean.CTMU.Symbol
import HeytingLean.CTMU.LogicStrat
import HeytingLean.LoF.Nucleus

/-
Compile-only: CTMU scaffold sanity.
-/

namespace HeytingLean
namespace Tests
namespace CTMU

open HeytingLean.CTMU
open HeytingLean.LoF

section Generic
variable {α : Type u} [PrimaryAlgebra α]
variable (R : Reentry α)

def _stableAlias : Type u := Stable (R := R)
def _telesisAlias : Type u := Telesis (R := R)

-- universe spec remains library-only; no construction in sanity test

def _symbolDemo : Symbol := { z := { real := 1.0, imag := 0.0 }, isNonZero := True }

def _kind1 : LogicKind := kind ⟨1⟩
def _kind3 : LogicKind := kind ⟨3⟩

end Generic

end CTMU
end Tests
end HeytingLean
