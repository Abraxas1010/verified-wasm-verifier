import HeytingLean.Genesis.NothingComputes.WitnessSeed

namespace HeytingLean.Tests.NothingComputes

open HeytingLean.Numbers.Surreal.NoneistKripke

def varyingWorld : World := { stage := 1, mode := .possible }

example :
    Nonempty (HeytingLean.Genesis.NothingComputes.DistinctionWitness .varying varyingWorld) := by
  exact HeytingLean.Genesis.NothingComputes.witness_from_plurality varyingWorld (by simp [varyingWorld])

example :
    let seed := HeytingLean.Genesis.NothingComputes.canonicalWitnessSeed varyingWorld (by simp [varyingWorld])
    IsAtom seed.seedRegion := by
  simpa using
    (HeytingLean.Genesis.NothingComputes.DistinctionWitness.seedRegion_atom
      (HeytingLean.Genesis.NothingComputes.canonicalWitnessSeed varyingWorld (by simp [varyingWorld])))

end HeytingLean.Tests.NothingComputes
