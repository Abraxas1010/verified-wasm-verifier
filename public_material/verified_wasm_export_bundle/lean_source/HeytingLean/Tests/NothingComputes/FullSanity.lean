import HeytingLean.Genesis.NothingComputes.FullChain
import HeytingLean.Tests.NothingComputes.YWitnessStrengthenedSanity
import HeytingLean.Tests.NothingComputes.ConsciousnessTowerSanity

namespace HeytingLean.Tests.NothingComputes

open Order
open HeytingLean.Genesis.YWitness

example :
    let milestone :=
      HeytingLean.Genesis.NothingComputes.fullMilestone
        (⊤ : Nucleus Bool) topWitness topSeed varyingWorld
        HeytingLean.Numbers.SurrealCore.nullCut false sampleProgram system
    milestone.noneism ∧ milestone.witness ∧ milestone.universality ∧
      milestone.strengthened ∧ milestone.preferredBasis ∧ milestone.consciousness := by
  exact HeytingLean.Genesis.NothingComputes.full_formalization
    (R := (⊤ : Nucleus Bool))
    (cw := topWitness)
    (hcw := follows_refl _)
    (seed := topSeed)
    (hseed := rfl)
    (w := varyingWorld)
    (hw := by simp [varyingWorld])
    (g := HeytingLean.Numbers.SurrealCore.nullCut)
    (a := false)
    (program := sampleProgram)
    (system := system)
    (hsystem := by
      show 2 ≤ system.tower.reflectiveDepth
      rfl)

end HeytingLean.Tests.NothingComputes
