import HeytingLean.Epiplexity.MDL

namespace HeytingLean
namespace Epiplexity

open scoped BigOperators

noncomputable section

open HeytingLean.Epiplexity.Info

variable {α : Type u} [Fintype α]

/-- An explicit witness of an MDL-optimal program with the paper's "shortest program" tie-break. -/
structure OptimalProg (T : Nat) (X : Probability.InfoTheory.FinDist α) where
  P : Prog α
  feasible : Prog.Feasible T P
  optimal : ∀ Q : Prog α, Prog.Feasible T Q → mdlCost X P ≤ mdlCost X Q
  tieBreak : ∀ Q : Prog α, Prog.Feasible T Q → mdlCost X Q = mdlCost X P → P.codeLen ≤ Q.codeLen

namespace OptimalProg

variable {T : Nat} {X : Probability.InfoTheory.FinDist α}

/-- Epiplexity `S_T(X)` (paper Definition 8) for an explicit optimizer witness. -/
def ST (opt : OptimalProg (α := α) T X) : Nat :=
  opt.P.codeLen

/-- Time-bounded entropy `H_T(X)` (paper Definition 8) for an explicit optimizer witness. -/
def HT (opt : OptimalProg (α := α) T X) : ℝ :=
  Info.crossEntropyBits X opt.P.dist

/-- Total time-bounded information `MDL_T(X) = S_T(X) + H_T(X)`. -/
def MDLT (opt : OptimalProg (α := α) T X) : ℝ :=
  (opt.ST : ℝ) + opt.HT

@[simp] theorem ST_nonneg (opt : OptimalProg (α := α) T X) : 0 ≤ opt.ST :=
  Nat.zero_le _

theorem HT_nonneg (opt : OptimalProg (α := α) T X) : 0 ≤ opt.HT :=
  Info.crossEntropyBits_nonneg (p := X) (q := opt.P.dist) opt.P.distPos

@[simp] theorem MDLT_eq_mdlCost (opt : OptimalProg (α := α) T X) :
    opt.MDLT = mdlCost X opt.P := by
  rfl

end OptimalProg

end

end Epiplexity
end HeytingLean
