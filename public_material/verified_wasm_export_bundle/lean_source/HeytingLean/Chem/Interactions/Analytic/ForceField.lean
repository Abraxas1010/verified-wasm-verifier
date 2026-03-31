import HeytingLean.Chem.Interactions.Analytic.Geometry
import HeytingLean.Chem.Interactions.Analytic.Potentials
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic

/-!
# Analytic (Real) force fields

This is an analytic counterpart of `HeytingLean.Chem.Interactions.ForceField`:
we compute pair distances from explicit 3D positions and sum Real-valued
pair potentials over unordered pairs.
-/

namespace HeytingLean.Chem.Interactions.Analytic

open BigOperators
open HeytingLean.Chem

noncomputable section

structure ForceField where
  pair : PairPotential

structure Configuration (n : Nat) where
  atoms : Fin n → Atom
  pos   : Fin n → Vec3

def pairIndexSet (n : Nat) : Finset (Fin n × Fin n) :=
  (Fintype.elems (α := Fin n)).product (Fintype.elems (α := Fin n)) |>.filter (fun p => p.1 < p.2)

def pairDist {n : Nat} (cfg : Configuration n) (i j : Fin n) : Scalar :=
  HeytingLean.Chem.Interactions.Analytic.dist (cfg.pos i) (cfg.pos j)

def totalPairEnergy {n : Nat} (ff : ForceField) (cfg : Configuration n) : Scalar :=
  (pairIndexSet n).sum (fun p =>
    ff.pair (cfg.atoms p.1) (cfg.atoms p.2) (pairDist cfg p.1 p.2)
  )

end

end HeytingLean.Chem.Interactions.Analytic
