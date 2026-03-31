import HeytingLean.Moonshine.Lattice.VOA
import HeytingLean.Moonshine.MoonshineModule.VNatural

set_option autoImplicit false

noncomputable section

namespace HeytingLean.Moonshine.Lattice

example : zeroPairingEvenLattice.rank = 1 := rfl

example : Rootless zeroPairingEvenLattice :=
  rootless_zeroPairingEvenLattice

example : toyLatticeVOA.L.rank = 1 := rfl

example (x : toyLatticeVOA.L.Λ) : toyLatticeVOA.latticeWeight x = 0 := by
  simp

example (Vn : HeytingLean.Moonshine.VNaturalData) : Vn.leech.L.rank = 24 := by
  exact Vn.rank_eq_24

end HeytingLean.Moonshine.Lattice
