import HeytingLean.Moonshine.Lattice.Leech
import HeytingLean.Moonshine.VOA.Grading

set_option autoImplicit false

noncomputable section

namespace HeytingLean.Moonshine.Lattice

open HeytingLean.Moonshine.VOA

/--
Minimal interface for a lattice VOA package: an underlying even lattice, a VOA, and a
weight map indexed by lattice vectors.
-/
structure LatticeVOAData where
  L : EvenLattice
  A : VOAData
  grading : WeightGrading A
  latticeWeight : L.Λ → ℤ
  latticeWeight_neg : ∀ x : L.Λ, latticeWeight (-x) = latticeWeight x

/--
Executable toy model for Gate C API checks.

This uses the zero-pairing lattice and the scalar toy VOA from Gate B.
-/
def toyLatticeVOA : LatticeVOAData where
  L := zeroPairingEvenLattice
  A := scalarVOA
  grading := scalarWeightGrading
  latticeWeight := fun _ => 0
  latticeWeight_neg := by
    intro x
    simp

@[simp] lemma toyLatticeVOA_latticeWeight (x : toyLatticeVOA.L.Λ) :
    toyLatticeVOA.latticeWeight x = 0 := by
  rfl

end HeytingLean.Moonshine.Lattice
