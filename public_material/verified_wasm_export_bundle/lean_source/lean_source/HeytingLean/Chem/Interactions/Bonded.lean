import HeytingLean.Chem.Bonding.BondGraph
import HeytingLean.Chem.Interactions.ForceField
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Bonded interactions (computable layer)

This file defines a minimal *bonded* term family that complements the existing
nonbonded pair-potentials/force-field layer. We keep it computable by working
over `ℚ` and taking distances from the configuration.

For geometry-derived Real distances, see the analytic layer:
`HeytingLean.Chem.Interactions.Analytic.Bonded`.
-/

namespace HeytingLean.Chem.Interactions

open BigOperators
open HeytingLean.Chem
open HeytingLean.Chem.Bonding

/-- Harmonic bond-stretch parameters (Hooke-like spring). -/
structure HarmonicBondParams where
  k  : Scalar
  r0 : Scalar
deriving Repr, DecidableEq

/-- Harmonic bond-stretch energy for a single bond length `r`. -/
def harmonicBondEnergy (p : HarmonicBondParams) (r : Scalar) : Scalar :=
  p.k * (r - p.r0) ^ (2 : Nat)

/-- Total bond-stretch energy for a bond graph and a distance-supplying configuration. -/
def totalBondStretchEnergy {n : Nat}
    (g : BondGraph n) (cfg : Configuration n) (param : BondEdge n → HarmonicBondParams) : Scalar :=
  g.bonds.sum (fun e => harmonicBondEnergy (param e) (cfg.dist e.i e.j))

end HeytingLean.Chem.Interactions

