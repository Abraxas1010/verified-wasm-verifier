import Mathlib.Probability.StrongLaw
import HeytingLean.Economics.Kelly.Core

namespace HeytingLean
namespace Economics
namespace Kelly

noncomputable section

open scoped BigOperators
open scoped Topology

open Filter MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

def logReturnSeq (f : ℝ) (R : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => Real.log (returnFactor f R n ω)

theorem strong_law_ae_real_logReturnSeq
    (f : ℝ) (R : ℕ → Ω → ℝ)
    (hint : Integrable (logReturnSeq (Ω := Ω) f R 0) μ)
    (hindep :
      Pairwise fun i j : ℕ =>
        IndepFun (logReturnSeq (Ω := Ω) f R i) (logReturnSeq (Ω := Ω) f R j) μ)
    (hident :
      ∀ i, IdentDistrib (logReturnSeq (Ω := Ω) f R i)
            (logReturnSeq (Ω := Ω) f R 0) μ μ) :
  ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, logReturnSeq (Ω := Ω) f R i ω) / n)
        atTop (𝓝 μ[logReturnSeq (Ω := Ω) f R 0]) := by
  let X : ℕ → Ω → ℝ := fun n ω => logReturnSeq (Ω := Ω) f R n ω
  have hident' : ∀ i, IdentDistrib (X i) (X 0) μ μ := by
    simpa [X] using hident
  simpa [X, logReturnSeq] using
    (ProbabilityTheory.strong_law_ae_real (μ := μ) (X := X) hint
      (hindep := by simpa [X, Function.onFun] using hindep)
      (hident := hident'))

theorem wealth_log_growth_ae_tendsto_of_strongLaw
    (W0 f : ℝ) (R : ℕ → Ω → ℝ)
    (hW0 : 0 < W0)
    (hpos : ∀ᵐ ω ∂μ, ∀ n, 0 < returnFactor f R n ω)
    (hint : Integrable (logReturnSeq (Ω := Ω) f R 0) μ)
    (hindep :
      Pairwise fun i j : ℕ =>
        IndepFun (logReturnSeq (Ω := Ω) f R i) (logReturnSeq (Ω := Ω) f R j) μ)
    (hident :
      ∀ i, IdentDistrib (logReturnSeq (Ω := Ω) f R i)
            (logReturnSeq (Ω := Ω) f R 0) μ μ) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ =>
          (Real.log (wealthR (Ω := Ω) W0 f R n ω) - Real.log W0) / n)
        atTop (𝓝 μ[logReturnSeq (Ω := Ω) f R 0]) := by
  have hsl :
      ∀ᵐ ω ∂μ,
        Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, logReturnSeq (Ω := Ω) f R i ω) / n)
          atTop (𝓝 μ[logReturnSeq (Ω := Ω) f R 0]) :=
    strong_law_ae_real_logReturnSeq (Ω := Ω) (μ := μ) (f := f) (R := R) hint hindep hident
  filter_upwards [hpos, hsl] with ω hposω hslω
  have hEq :
      (fun n : ℕ =>
          (Real.log (wealthR (Ω := Ω) W0 f R n ω) - Real.log W0) / n)
        =
      (fun n : ℕ =>
          (∑ i ∈ Finset.range n, logReturnSeq (Ω := Ω) f R i ω) / n) := by
    funext n
    have hfac : ∀ i < n, 0 < returnFactor f R i ω := by
      intro i _hi
      exact hposω i
    simp [logReturnSeq,
      log_wealthR_sub_logW0_eq_sum_log_returnFactor (Ω := Ω)
        (W0 := W0) (f := f) (R := R) (n := n) (ω := ω) hW0 hfac]
  simpa [hEq] using hslω

end

end Kelly
end Economics
end HeytingLean
