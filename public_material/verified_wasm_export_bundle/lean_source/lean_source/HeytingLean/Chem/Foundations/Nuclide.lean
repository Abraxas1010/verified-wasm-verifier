import HeytingLean.Chem.PeriodicTable.Elements

namespace HeytingLean.Chem

open HeytingLean.Chem.PeriodicTable

-- A nuclide (Z protons + N neutrons), represented by (element, mass number A = Z + N).
structure Nuclide where
  element : PeriodicTable.Element
  massNumber : Nat
deriving Repr, DecidableEq

def Nuclide.atomicNumber (n : Nuclide) : Nat :=
  PeriodicTable.atomicNumber n.element

def Nuclide.neutronNumber (n : Nuclide) : Nat :=
  n.massNumber - n.atomicNumber

end HeytingLean.Chem

