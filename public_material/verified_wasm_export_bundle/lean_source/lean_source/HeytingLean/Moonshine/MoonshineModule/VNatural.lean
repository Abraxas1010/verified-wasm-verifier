import HeytingLean.Moonshine.Lattice.VOA
import HeytingLean.Moonshine.VOA.Modules

set_option autoImplicit false

noncomputable section

namespace HeytingLean.Moonshine

open HeytingLean.Moonshine.Lattice
open HeytingLean.Moonshine.VOA

/--
Abstract data for a `ℤ₂`-orbifold extension step over a lattice VOA.

This keeps the Gate C API explicit while avoiding any global existence axioms.
-/
structure OrbifoldData where
  base : LatticeVOAData
  twisted : VOARep base.A
  fixedWeightOneTrivial : Prop := True

/--
Kernel-pure interface target for the moonshine module `V^natural`.

At this stage we only package the Leech-lattice input and an orbifold extension witness.
-/
structure VNaturalData where
  leech : LeechLatticeData
  orbifold : OrbifoldData

namespace VNaturalData

@[simp] lemma rank_eq_24 (Vn : VNaturalData) : Vn.leech.L.rank = 24 :=
  Vn.leech.rank_eq

end VNaturalData

end HeytingLean.Moonshine
