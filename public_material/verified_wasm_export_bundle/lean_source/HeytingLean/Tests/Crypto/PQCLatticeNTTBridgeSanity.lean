import HeytingLean.Crypto.Lattice.NTTBridge

namespace HeytingLean.Tests.Crypto.PQCLatticeNTTBridgeSanity

open HeytingLean.Crypto.Lattice.NTTBridge

abbrev F : Type := ZMod HeytingLean.Crypto.Lattice.NTT.q

example (a b zk : F) :
    let (u, v) := HeytingLean.Crypto.Lattice.NTTIterative.butterfly a b zk
    u = a + zk * b ∧ v = a - zk * b :=
  butterfly_algebraic (a := a) (b := b) (zk := zk)

end HeytingLean.Tests.Crypto.PQCLatticeNTTBridgeSanity

