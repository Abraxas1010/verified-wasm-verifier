import HeytingLean.Chem.Bonding.Atoms
import HeytingLean.Chem.Bonding.BondTypes
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace HeytingLean.Chem.Bonding

open HeytingLean.Chem
open scoped BigOperators

/-!
# Bond graphs (combinatorial chemistry layer)

This layer models a molecule/material basis as a finite set of atoms plus a finite
set of typed bonds between atom indices.

It intentionally does *not* commit to any particular bonding semantics (orbitals,
energetics, QED corrections). Those are added in higher layers.
-/

structure BondEdge (n : Nat) where
  i : Fin n
  j : Fin n
  ty : BondType := {}
deriving Repr, DecidableEq

structure BondGraph (n : Nat) where
  atoms : Fin n -> Atom
  bonds : Finset (BondEdge n)

namespace BondGraph

def Valid {n : Nat} (g : BondGraph n) : Prop :=
  ∀ e, e ∈ g.bonds -> e.i ≠ e.j

def degree {n : Nat} (g : BondGraph n) (v : Fin n) : Nat :=
  (g.bonds.filter (fun e => e.i = v ∨ e.j = v)).card

def valenceDegree {n : Nat} (g : BondGraph n) (v : Fin n) : Nat :=
  (g.bonds.filter (fun e => e.i = v ∨ e.j = v)).sum (fun e => e.ty.orderWeight)

end BondGraph

end HeytingLean.Chem.Bonding
