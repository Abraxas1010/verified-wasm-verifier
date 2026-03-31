import HeytingLean.FractalUniverse.Extraction.SpectralComputer
import HeytingLean.FractalUniverse.Core.SpectralDimension

/-!
# Corrected Spectral Dimension via Diagonal Return Probability

REUSABLE ABSTRACTION: defines the spectral dimension using the
correct diagonal return probability `returnProbDiag` (P^σ(v,v))
from SpectralComputer, rather than `Core.returnProb` which computes
P^σ·1 = 1 for all stochastic matrices (a known flaw).

## Content

- `spectralDimRatioCorrect`: D_s = -2 · log P^σ(v,v) / log σ
  using the corrected `returnProbDiag`
- `HasCorrectSpectralDimValue`: the limit definition using the
  corrected ratio
- `returnProbDiag_log_well_defined`: P^σ(v,v) ∈ [0,1] (direct
  reuse of SpectralComputer theorem)

## Scope note

The full PSL bridge (heat kernel trace = Σ exp(-λ_k σ) connecting
Laplacian eigenvalues to return probabilities) requires matrix
exponential infrastructure and is a follow-on conjecture.
-/

namespace HeytingLean.FractalUniverse.Bridges

open Extraction Core

/-- The spectral dimension via the correct diagonal return probability.
    `returnProbDiag` gives the mathematically correct P^σ(v,v)
    (diagonal entry of iterated transition matrix), fixing the flaw in
    `Core.spectralDimRatio` which uses `returnProb` (always = 1). -/
noncomputable def spectralDimRatioCorrect {G : DynamicGraph} {t : ℕ}
    [Fintype (G.V t)] [DecidableEq (G.V t)]
    (W : RandomWalk G t) (v : G.V t) (σ : ℕ) : ℝ :=
  if σ = 0 then 0
  else -2 * Real.log (returnProbDiag W v σ) / Real.log σ

/-- The corrected spectral dimension: the limit of the corrected ratio. -/
def HasCorrectSpectralDimValue {G : DynamicGraph} {t : ℕ}
    [Fintype (G.V t)] [DecidableEq (G.V t)]
    (W : RandomWalk G t) (v : G.V t) (D_s : ℝ) : Prop :=
  Filter.Tendsto (fun σ : ℕ => spectralDimRatioCorrect W v σ)
    Filter.atTop (nhds D_s)

/-- returnProbDiag lies in [0,1]: direct reuse of SpectralComputer. -/
theorem returnProbDiag_log_well_defined {G : DynamicGraph} {t : ℕ}
    [Fintype (G.V t)] [DecidableEq (G.V t)]
    (W : RandomWalk G t) (v : G.V t) (σ : ℕ) :
    0 ≤ returnProbDiag W v σ ∧ returnProbDiag W v σ ≤ 1 :=
  returnProbDiag_unit_interval W v σ

/-- The corrected ratio at σ = 0 is 0 (by convention). -/
theorem spectralDimRatioCorrect_zero {G : DynamicGraph} {t : ℕ}
    [Fintype (G.V t)] [DecidableEq (G.V t)]
    (W : RandomWalk G t) (v : G.V t) :
    spectralDimRatioCorrect W v 0 = 0 := by
  simp [spectralDimRatioCorrect]

end HeytingLean.FractalUniverse.Bridges
