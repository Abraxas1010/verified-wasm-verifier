import HeytingLean.Chem.PeriodicTable.CIAAW2024
import Mathlib.Data.Int.Basic

namespace HeytingLean.Chem

open HeytingLean.Chem.PeriodicTable

-- Minimal atom/ion record: element + integer charge.
structure Atom where
  element : PeriodicTable.Element
  charge : Int := 0
deriving Repr, DecidableEq

def Atom.atomicNumber (a : Atom) : Nat :=
  PeriodicTable.atomicNumber a.element

def Atom.symbol (a : Atom) : String :=
  PeriodicTable.symbol a.element

def Atom.name (a : Atom) : String :=
  PeriodicTable.name a.element

end HeytingLean.Chem

