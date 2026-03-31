import HeytingLean.Magma.Numbers.Natural
import Mathlib.SetTheory.Ordinal.Basic

namespace HeytingLean.Magma.Numbers

open HeytingLean.Magma

variable {A : Type*} [MagmaticAtoms A] [u : MagmaticUniverse A] [PairEncoding A] [ProductEncoding A]
  [NaturalPresentation A]

class OrdinalPresentation (A : Type*) [MagmaticAtoms A] [MagmaticUniverse A]
    [PairEncoding A] [ProductEncoding A] [NaturalPresentation A] where
  mordinal : Ordinal → Magma A
  mordinal_order : ∀ {α β : Ordinal}, α < β ↔ mordinal α < mordinal β

variable [OrdinalPresentation A]

def mordinal (α : Ordinal) : Magma A := OrdinalPresentation.mordinal (A := A) α

theorem mordinal_order (α β : Ordinal) :
    α < β ↔ mordinal (A := A) α < mordinal (A := A) β :=
  OrdinalPresentation.mordinal_order

end HeytingLean.Magma.Numbers
