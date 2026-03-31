import HeytingLean.Chem.Interactions.Potentials
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic

namespace HeytingLean.Chem.Interactions

open BigOperators
open HeytingLean.Chem

/-!
# Force fields (spec-level + computable)

To stay computable, we do not define geometric distances here. Instead, a
configuration supplies pairwise distances (e.g. computed externally or by a
separate analytic layer).
-/

structure ForceField where
  pair : PairPotential

structure Configuration (n : Nat) where
  atoms : Fin n -> Atom
  dist : Fin n -> Fin n -> Scalar

def pairIndexSet (n : Nat) : Finset (Fin n × Fin n) :=
  (Fintype.elems (α := Fin n)).product (Fintype.elems (α := Fin n)) |>.filter (fun p => p.1 < p.2)

def totalPairEnergy {n : Nat} (ff : ForceField) (cfg : Configuration n) : Scalar :=
  (pairIndexSet n).sum (fun p =>
    ff.pair (cfg.atoms p.1) (cfg.atoms p.2) (cfg.dist p.1 p.2)
  )

end HeytingLean.Chem.Interactions
