import HeytingLean.Crypto.Lattice.NTTCorrectness

/-!
# PQC lattice bridge sanity: NTT correctness (algebraic)

This is a compile-time sanity check: importing `NTTCorrectness` forces the CRT-based NTT proof
to elaborate as part of the default build umbrella.
-/

namespace HeytingLean.Tests.Crypto.PQCLatticeNTTCorrectnessSanity

open HeytingLean.Crypto.Lattice.NTTCorrectness

-- Smoke: `invNTT ∘ NTT = id` at the stated type.
example (x : Rq) : invNTT (NTT x) = x := by
  simpa using invNTT_NTT (x := x)

end HeytingLean.Tests.Crypto.PQCLatticeNTTCorrectnessSanity

