import Mathlib.Analysis.SpecialFunctions.Exp
import HeytingLean.Chem.Interactions.Analytic.Geometry
import HeytingLean.Chem.Bonding.Atoms

/-!
# Analytic (Real) pair potentials

These are Real-valued potentials intended for specification-level reasoning or
bridges to numeric engines. Keep them separate from the computable `ℚ` layer.
-/

namespace HeytingLean.Chem.Interactions.Analytic

noncomputable section

open HeytingLean.Chem

abbrev PairPotential : Type := Atom → Atom → Scalar → Scalar

structure LennardJonesParams where
  epsilon : Scalar
  sigma   : Scalar

def lennardJones (p : LennardJonesParams) : PairPotential :=
  fun _ _ r =>
    4 * p.epsilon * ((p.sigma / r) ^ (12 : Nat) - (p.sigma / r) ^ (6 : Nat))

structure CoulombParams where
  k : Scalar

def coulomb (p : CoulombParams) : PairPotential :=
  fun a b r =>
    p.k * ((a.charge : Int) : Scalar) * ((b.charge : Int) : Scalar) / r

/-!
Morse potential:

  V(r) = D_e * (exp(-2 a (r - r_e)) - 2 exp(-a (r - r_e)))
-/
structure MorseParams where
  De : Scalar
  a  : Scalar
  re : Scalar

def morse (p : MorseParams) : PairPotential :=
  fun _ _ r =>
    let x := r - p.re
    p.De * (Real.exp (-2 * p.a * x) - 2 * Real.exp (-p.a * x))

end

end HeytingLean.Chem.Interactions.Analytic
