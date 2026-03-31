import Mathlib.Order.ConditionallyCompleteLattice.Defs
import HeytingLean.Epiplexity.Info
import HeytingLean.Epiplexity.Programs

namespace HeytingLean
namespace Epiplexity

open scoped BigOperators

noncomputable section

open HeytingLean.Epiplexity.Info

variable {α : Type u} [Fintype α]

/-- Two-part MDL cost in bits: `|P| + E_X[-log₂ P(X)]`. -/
def mdlCost (X : Probability.InfoTheory.FinDist α) (P : Prog α) : ℝ :=
  (P.codeLen : ℝ) + Info.crossEntropyBits X P.dist

/-- The set of MDL costs achieved by feasible programs. -/
def mdlCostSet (T : Nat) (X : Probability.InfoTheory.FinDist α) : Set ℝ :=
  {c | ∃ P : Prog α, Prog.Feasible T P ∧ mdlCost X P = c}

/-- Infimum MDL value over feasible programs (in bits). -/
def MDLinf (T : Nat) (X : Probability.InfoTheory.FinDist α) : ℝ :=
  sInf (mdlCostSet (α := α) T X)

theorem mdlCost_nonneg (X : Probability.InfoTheory.FinDist α) (P : Prog α) : 0 ≤ mdlCost X P := by
  have hlen : (0 : ℝ) ≤ (P.codeLen : ℝ) := by exact_mod_cast Nat.zero_le _
  have hce : 0 ≤ Info.crossEntropyBits X P.dist :=
    Info.crossEntropyBits_nonneg (p := X) (q := P.dist) P.distPos
  exact add_nonneg hlen hce

theorem mdlCostSet_bddBelow (T : Nat) (X : Probability.InfoTheory.FinDist α) :
    BddBelow (mdlCostSet (α := α) T X) := by
  refine ⟨0, ?_⟩
  intro c hc
  rcases hc with ⟨P, _hP, rfl⟩
  exact mdlCost_nonneg (X := X) (P := P)

theorem MDLinf_le_mdlCost (T : Nat) (X : Probability.InfoTheory.FinDist α)
    (P : Prog α) (hP : Prog.Feasible T P) :
    MDLinf (α := α) T X ≤ mdlCost X P := by
  exact csInf_le (mdlCostSet_bddBelow (α := α) T X) ⟨P, hP, rfl⟩

end

end Epiplexity
end HeytingLean
