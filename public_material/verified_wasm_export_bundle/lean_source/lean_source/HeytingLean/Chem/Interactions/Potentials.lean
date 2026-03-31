import HeytingLean.Chem.Bonding.Atoms
import Mathlib.Data.Rat.Defs

namespace HeytingLean.Chem.Interactions

open HeytingLean.Chem

/-!
# Classical interaction potentials (computable layer)

We keep this layer computable (C-backend friendly) by working over `ℚ`.
More analytic models (e.g. with `exp`, `sqrt`, etc.) should live in a separate
"analysis" layer or be represented symbolically.
-/

abbrev Scalar : Type := ℚ

abbrev PairPotential : Type := Atom -> Atom -> Scalar -> Scalar

structure LennardJonesParams where
  epsilon : Scalar
  sigma : Scalar
deriving Repr, DecidableEq

def lennardJones (p : LennardJonesParams) : PairPotential :=
  fun _ _ r =>
    if r = 0 then
      0
    else
      let x := p.sigma / r
      4 * p.epsilon * (x ^ (12 : Nat) - x ^ (6 : Nat))

structure CoulombParams where
  k : Scalar
deriving Repr, DecidableEq

def coulomb (p : CoulombParams) : PairPotential :=
  fun a b r =>
    if r = 0 then
      0
    else
      p.k * (a.charge : Scalar) * (b.charge : Scalar) / r

end HeytingLean.Chem.Interactions

