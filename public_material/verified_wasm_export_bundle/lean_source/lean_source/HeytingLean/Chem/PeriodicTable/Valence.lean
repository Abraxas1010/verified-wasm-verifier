import HeytingLean.Chem.PeriodicTable.Properties

/-!
# Valence and periodic-table layout helpers

This file provides small wrappers around `PeriodicTable.modelProperties` so downstream
modules (bonding/materials) can depend on stable identifiers without importing the
entire properties implementation details.
-/

namespace HeytingLean
namespace Chem
namespace PeriodicTable

def period (e : Element) : Nat :=
  (modelProperties e).period

def block (e : Element) : Orbital :=
  (modelProperties e).block

def iupacGroup? (e : Element) : Option Nat :=
  (modelProperties e).iupacGroup?

def valenceElectrons (e : Element) : Nat :=
  (modelProperties e).valenceElectrons

end PeriodicTable
end Chem
end HeytingLean

