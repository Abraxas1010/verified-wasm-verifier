import HeytingLean.Probability.InfoTheory.FinDist

namespace HeytingLean
namespace Silicon

noncomputable section

open scoped BigOperators

open HeytingLean.Probability.InfoTheory

universe u

/-- Core data of a “measurement run”: a finite joint distribution over internal state `S`
and observable output `O`. -/
abbrev Run (S O : Type u) [Fintype S] [Fintype O] :=
  FinDist (S × O)

namespace Run

variable {S O : Type u} [Fintype S] [Fintype O]

/-- The internal-state marginal `P_S` of a run `P_{S,O}`. -/
abbrev stateMarginal (P : Run S O) : FinDist S :=
  FinDist.marginalLeft (α := S) (β := O) P

/-- The observable marginal `P_O` of a run `P_{S,O}`. -/
abbrev obsMarginal (P : Run S O) : FinDist O :=
  FinDist.marginalRight (α := S) (β := O) P

end Run

end
end Silicon
end HeytingLean

