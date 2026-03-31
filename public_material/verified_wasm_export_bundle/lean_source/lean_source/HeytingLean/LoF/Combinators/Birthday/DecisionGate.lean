import HeytingLean.LoF.Combinators.Birthday.Metric

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Birthday

open HeytingLean.LoF

structure BirthdaySample where
  structuralBirthday : Nat
  sourceNodes : Nat
  reducedNodes : Nat
  stepChoices : Nat
  deriving Repr

/-- Deterministic sample surface for bounded SKY birthday experiments. -/
def measureSample (fuel : Nat) (t : Comb) : BirthdaySample :=
  let reduced := SKYExec.reduceFuel fuel t
  { structuralBirthday := combBirthday t
    sourceNodes := combNodeCount t
    reducedNodes := combNodeCount reduced
    stepChoices := stepBranching t }

def baselineSamples : List BirthdaySample :=
  [ measureSample 4 Comb.K
  , measureSample 4 (Comb.app Comb.Y Comb.K)
  , measureSample 6 (Comb.app Comb.I Comb.K) ]

@[simp] theorem measureSample_structuralBirthday (fuel : Nat) (t : Comb) :
    (measureSample fuel t).structuralBirthday = combBirthday t := by
  rfl

@[simp] theorem measureSample_sourceNodes_pos (fuel : Nat) (t : Comb) :
    0 < (measureSample fuel t).sourceNodes := by
  show 0 < combNodeCount t
  exact combNodeCount_pos t

@[simp] theorem baselineSamples_nonempty : baselineSamples ≠ [] := by
  simp [baselineSamples]

end Birthday
end Combinators
end LoF
end HeytingLean
