import HeytingLean.Quantum.NothingComputes.PreferredBasis

namespace HeytingLean.Tests.NothingComputes

example :
    HeytingLean.Quantum.NothingComputes.BasisCandidate Bool
      (HeytingLean.Quantum.NothingComputes.preferredSelector Bool false) := by
  exact HeytingLean.Quantum.NothingComputes.preferredSelector_is_basisCandidate Bool false

example :
    Nonempty (HeytingLean.Quantum.NothingComputes.EigenformFamily Bool) := by
  exact HeytingLean.Quantum.NothingComputes.many_eigenforms_of_distinct_candidates
    Bool
    (x := HeytingLean.Quantum.NothingComputes.preferredSelector Bool false)
    (y := HeytingLean.Quantum.NothingComputes.preferredSelector Bool true)
    (HeytingLean.Quantum.NothingComputes.preferredSelector_is_basisCandidate Bool false)
    (HeytingLean.Quantum.NothingComputes.preferredSelector_is_basisCandidate Bool true)
    (by simp [HeytingLean.Quantum.NothingComputes.preferredSelector])

end HeytingLean.Tests.NothingComputes
