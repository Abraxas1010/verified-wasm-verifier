import Mathlib.Data.String.Basic
import HeytingLean.Chem.Foundations.Terms

/-!
# Bonding (chemistry-facing) definitions

We separate chemistry-facing terminology ("bond", "species", identifiers) from the QED/physics
layer. Later modules can define *derived* quantities (e.g. bond dissociation energy) in terms of a
chosen Hamiltonian model, while keeping the chemistry vocabulary stable and provenance-backed.
-/

namespace HeytingLean
namespace Chem
namespace Bonding

open HeytingLean.Chem.Foundations

/-- An opaque chemical identifier. We start with strings (InChI/SMILES/etc.) and refine later. -/
structure ChemId where
  scheme : String := "opaque"
  value  : String

/-- A chemical species (molecule, ion, etc.) at the "identifier + metadata" level. -/
structure Species where
  id    : ChemId
  label : String := ""

/-- A "bond" record in the minimal graph sense (endpoints are atom indices in some species encoding).

At M0 this is purely combinatorial; semantics (energetic, orbital, QED-derived) comes later. -/
structure Bond where
  a1 : Nat
  a2 : Nat
  kind : String := "unspecified"
  term : Term := chemicalBondTerm

end Bonding
end Chem
end HeytingLean

