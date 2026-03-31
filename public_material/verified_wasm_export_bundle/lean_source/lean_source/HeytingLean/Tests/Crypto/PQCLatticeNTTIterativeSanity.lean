import HeytingLean.Crypto.Lattice.NTTIterative

/-!
# PQC lattice bridge sanity: iterative NTT (algorithm skeleton)

This is a compile-time sanity check: importing `NTTIterative` ensures the algorithmic NTT
definition elaborates as part of the default build umbrella.
-/

namespace HeytingLean.Tests.Crypto.PQCLatticeNTTIterativeSanity

open HeytingLean.Crypto.Lattice.NTTIterative

example : (zetaTable.size = 128) := by
  simp [zetaTable]

end HeytingLean.Tests.Crypto.PQCLatticeNTTIterativeSanity
