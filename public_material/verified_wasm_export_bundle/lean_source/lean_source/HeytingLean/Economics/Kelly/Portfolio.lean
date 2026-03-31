import Mathlib.Data.Fintype.BigOperators
import HeytingLean.Economics.Kelly.Asymptotic

namespace HeytingLean
namespace Economics
namespace Kelly

noncomputable section

open scoped BigOperators
open scoped Topology

open Filter MeasureTheory ProbabilityTheory

variable {Ω : Type*}
variable {Asset : Type*} [Fintype Asset]

def portfolioReturn (w : Asset → ℝ) (R : ℕ → Ω → Asset → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ a : Asset, w a * R n ω a

def wealthPortfolio (W0 : ℝ) (w : Asset → ℝ) (R : ℕ → Ω → Asset → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  wealthR (Ω := Ω) W0 1 (portfolioReturn (Asset := Asset) w R) n ω

def logPortfolioReturnSeq (w : Asset → ℝ) (R : ℕ → Ω → Asset → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => Real.log (returnFactor (Ω := Ω) 1 (portfolioReturn (Asset := Asset) w R) n ω)

@[simp] lemma returnFactor_one_portfolioReturn (w : Asset → ℝ) (R : ℕ → Ω → Asset → ℝ)
    (n : ℕ) (ω : Ω) :
    returnFactor (Ω := Ω) 1 (portfolioReturn (Asset := Asset) w R) n ω
      = 1 + ∑ a : Asset, w a * R n ω a := by
  simp [returnFactor, portfolioReturn]

theorem wealthPortfolio_log_growth_ae_tendsto_of_strongLaw
    [MeasurableSpace Ω] {μ : Measure Ω}
    (W0 : ℝ) (w : Asset → ℝ) (R : ℕ → Ω → Asset → ℝ)
    (hW0 : 0 < W0)
    (hpos :
      ∀ᵐ ω ∂μ, ∀ n,
        0 < returnFactor (Ω := Ω) 1 (portfolioReturn (Asset := Asset) w R) n ω)
    (hint : Integrable (logPortfolioReturnSeq (Ω := Ω) (Asset := Asset) w R 0) μ)
    (hindep :
      Pairwise fun i j : ℕ =>
        IndepFun (logPortfolioReturnSeq (Ω := Ω) (Asset := Asset) w R i)
          (logPortfolioReturnSeq (Ω := Ω) (Asset := Asset) w R j) μ)
    (hident :
      ∀ i,
        IdentDistrib (logPortfolioReturnSeq (Ω := Ω) (Asset := Asset) w R i)
          (logPortfolioReturnSeq (Ω := Ω) (Asset := Asset) w R 0) μ μ) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ =>
        (Real.log (wealthPortfolio (Ω := Ω) (Asset := Asset) W0 w R n ω) - Real.log W0) / n)
        atTop (𝓝 μ[logPortfolioReturnSeq (Ω := Ω) (Asset := Asset) w R 0]) := by
  simpa [wealthPortfolio, logPortfolioReturnSeq, logReturnSeq] using
    (wealth_log_growth_ae_tendsto_of_strongLaw (Ω := Ω) (μ := μ)
      (W0 := W0) (f := (1 : ℝ))
      (R := portfolioReturn (Asset := Asset) w R)
      hW0 hpos hint hindep hident)

end

end Kelly
end Economics
end HeytingLean
