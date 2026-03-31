import HeytingLean.Chem.Bonding.BondGraph
import HeytingLean.Chem.Interactions.Analytic.ForceField
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Bonded interactions (analytic layer)

This is the Real/geometry counterpart of `HeytingLean.Chem.Interactions.Bonded`.
-/

namespace HeytingLean.Chem.Interactions.Analytic

open BigOperators
open HeytingLean.Chem
open HeytingLean.Chem.Bonding

noncomputable section

/-- Harmonic bond-stretch parameters (Hooke-like spring). -/
structure HarmonicBondParams where
  k  : Scalar
  r0 : Scalar

/-- Harmonic bond-stretch energy for a single bond length `r`. -/
def harmonicBondEnergy (p : HarmonicBondParams) (r : Scalar) : Scalar :=
  p.k * (r - p.r0) ^ (2 : Nat)

/-- Total bond-stretch energy for a bond graph and an analytic configuration. -/
def totalBondStretchEnergy {n : Nat}
    (g : BondGraph n) (cfg : Configuration n) (param : BondEdge n → HarmonicBondParams) : Scalar :=
  g.bonds.sum (fun e => harmonicBondEnergy (param e) (pairDist cfg e.i e.j))

end

end HeytingLean.Chem.Interactions.Analytic

