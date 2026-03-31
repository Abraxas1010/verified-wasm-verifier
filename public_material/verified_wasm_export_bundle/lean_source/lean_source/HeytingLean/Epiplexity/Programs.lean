import HeytingLean.Epiplexity.Prelude
import HeytingLean.Meta.AIT.Prefix

namespace HeytingLean
namespace Epiplexity

open HeytingLean.Meta.AIT

open scoped BigOperators

noncomputable section

variable {α : Type u} [Fintype α]

/-- A coded probabilistic model together with a (simplified) runtime cost. -/
structure Prog (α : Type u) [Fintype α] where
  code : Program
  runtime : Nat
  dist : Probability.InfoTheory.FinDist α
  distPos : dist.Pos

namespace Prog

variable {α : Type u} [Fintype α]

/-- Program length in bits. -/
def codeLen (P : Prog α) : Nat :=
  codeLength P.code

/-- Feasible under a time budget `T`. -/
def Feasible (T : Nat) (P : Prog α) : Prop :=
  P.runtime ≤ T

@[simp] theorem codeLen_nil (P : Prog α) (h : P.code = []) : P.codeLen = 0 := by
  simp [codeLen, h]

end Prog

end

end Epiplexity
end HeytingLean
