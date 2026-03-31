import HeytingLean.Chem.PeriodicTable.Proofs

namespace HeytingLean.Chem.Tests

open HeytingLean.Chem.PeriodicTable
open HeytingLean.Chem.PeriodicTable.Elements

-- Sanity: generated proofs are available and reduce.
example : atomicNumber Fe = 26 := by simp
example : name Og = "oganesson" := by simp

end HeytingLean.Chem.Tests

