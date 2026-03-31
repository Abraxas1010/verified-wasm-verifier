import HeytingLean.LoF.Combinators.Differential.GradientDescent

/-!
# ATP.DifferentiableATP.CoreOps

Shared core operations for differentiable ATP runtime:
- nucleus projection on combinator sums,
- projected gradient step.
-/

namespace HeytingLean
namespace ATP
namespace DifferentiableATP

open HeytingLean.LoF
open HeytingLean.LoF.Combinators.Differential
open HeytingLean.LoF.Combinators.Differential.Compute

def nucleusR : Comb → Comb
  | .app .K _ => .K
  | .app (.app .K _) _ => .K
  | .app .S _ => .S
  | t => t

def projectToFixedWeights (R : Comb → Comb) (w : FSum) : FSum :=
  w.filter (fun tc => decide (R tc.1 = tc.1))

theorem projectToFixedWeights_idempotent (R : Comb → Comb) (w : FSum) :
    projectToFixedWeights R (projectToFixedWeights R w) = projectToFixedWeights R w := by
  unfold projectToFixedWeights
  simp

def gradientStepProjected (config : GDConfig) (examples : List IOExample) (w : FSum) : FSum :=
  let stepped := Compute.gradientStep config examples w
  projectToFixedWeights nucleusR (stepped.map (fun tc => (tc.1, truncRat tc.2)))

/-- Lightweight fixed-subspace witness used by categorical/step-preservation plumbing. -/
def allFixedSubspace (R : Comb → Comb) (w : FSum) : Prop :=
  ∃ u : FSum, w = projectToFixedWeights R u

theorem projected_mem_fixed_subspace (R : Comb → Comb) (w : FSum) :
    allFixedSubspace R (projectToFixedWeights R w) := by
  exact ⟨w, rfl⟩

end DifferentiableATP
end ATP
end HeytingLean
