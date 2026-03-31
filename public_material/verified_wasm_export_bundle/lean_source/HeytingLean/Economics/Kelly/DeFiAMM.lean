import HeytingLean.DeFi.AMM
import HeytingLean.Economics.Kelly.Portfolio

namespace HeytingLean
namespace Economics
namespace Kelly

noncomputable section

open scoped BigOperators
open scoped Topology

open Filter MeasureTheory ProbabilityTheory

namespace DeFiAMM

open HeytingLean.DeFi

inductive Trade where
  | swapX (dx : ℚ)
  | swapY (dy : ℚ)
  deriving Repr

def applyTrade (p : DeFi.AMM.Params) (s : DeFi.AMM.State) : Trade → DeFi.AMM.State
  | Trade.swapX dx => DeFi.AMM.swapX p s dx
  | Trade.swapY dy => DeFi.AMM.swapY p s dy

def stateSeq {Ω : Type*} (p : DeFi.AMM.Params) (u : ℕ → Ω → Trade) (s0 : Ω → DeFi.AMM.State) :
    ℕ → Ω → DeFi.AMM.State :=
  fun n ω => Nat.rec (s0 ω) (fun k st => applyTrade p st (u k ω)) n

@[simp] lemma stateSeq_zero {Ω : Type*} (p : DeFi.AMM.Params) (u : ℕ → Ω → Trade)
    (s0 : Ω → DeFi.AMM.State) (ω : Ω) :
    stateSeq p u s0 0 ω = s0 ω := by
  simp [stateSeq]

lemma stateSeq_succ {Ω : Type*} (p : DeFi.AMM.Params) (u : ℕ → Ω → Trade)
    (s0 : Ω → DeFi.AMM.State) (n : ℕ) (ω : Ω) :
    stateSeq p u s0 (n + 1) ω = applyTrade p (stateSeq p u s0 n ω) (u n ω) := by
  simp [stateSeq]

def tradeDenomNonzero (p : DeFi.AMM.Params) (s : DeFi.AMM.State) : Trade → Prop
  | Trade.swapX dx => s.x + DeFi.AMM.gamma p * dx ≠ 0
  | Trade.swapY dy => s.y + DeFi.AMM.gamma p * dy ≠ 0

theorem stateSeq_invariant_of {Ω : Type*} {k₀ : ℚ}
    (p : DeFi.AMM.Params) (u : ℕ → Ω → Trade) (s0 : Ω → DeFi.AMM.State)
    (hInv0 : ∀ ω, DeFi.AMM.ConstantProductInvariant k₀ (s0 ω))
    (hDenom : ∀ n ω, tradeDenomNonzero p (stateSeq p u s0 n ω) (u n ω)) :
    ∀ n ω, DeFi.AMM.ConstantProductInvariant k₀ (stateSeq p u s0 n ω) := by
  intro n
  induction n with
  | zero =>
      intro ω
      simpa using hInv0 ω
  | succ n ih =>
      intro ω
      have hInvn : DeFi.AMM.ConstantProductInvariant k₀ (stateSeq p u s0 n ω) := ih ω
      have hstep : DeFi.AMM.ConstantProductInvariant k₀ (stateSeq p u s0 (n + 1) ω) := by
        classical
        cases htr : u n ω with
        | swapX dx =>
            have hDenom' :
                (stateSeq p u s0 n ω).x + DeFi.AMM.gamma p * dx ≠ 0 := by
              simpa [tradeDenomNonzero, htr] using hDenom n ω
            simpa [stateSeq_succ, applyTrade, htr] using
              DeFi.AMM.swapX_preserves_invariant (k₀ := k₀) p (stateSeq p u s0 n ω) dx hInvn hDenom'
        | swapY dy =>
            have hDenom' :
                (stateSeq p u s0 n ω).y + DeFi.AMM.gamma p * dy ≠ 0 := by
              simpa [tradeDenomNonzero, htr] using hDenom n ω
            simpa [stateSeq_succ, applyTrade, htr] using
              DeFi.AMM.swapY_preserves_invariant (k₀ := k₀) p (stateSeq p u s0 n ω) dy hInvn hDenom'
      simpa using hstep

def reserveQ (t : Bool) (s : DeFi.AMM.State) : ℚ :=
  if t then s.x else s.y

def reserveR (t : Bool) (s : DeFi.AMM.State) : ℝ :=
  (reserveQ t s : ℝ)

def ammReturn (p : DeFi.AMM.Params) {Ω : Type*} (u : ℕ → Ω → Trade) (s0 : Ω → DeFi.AMM.State) :
    ℕ → Ω → Bool → ℝ :=
  fun n ω t =>
    let s := stateSeq p u s0
    reserveR t (s (n + 1) ω) / reserveR t (s n ω) - 1

def wealthAMM (W0 : ℝ) (w : Bool → ℝ) (p : DeFi.AMM.Params) {Ω : Type*}
    (u : ℕ → Ω → Trade) (s0 : Ω → DeFi.AMM.State) : ℕ → Ω → ℝ :=
  wealthPortfolio (Ω := Ω) (Asset := Bool) W0 w (ammReturn p u s0)

def logAMMReturnSeq (w : Bool → ℝ) (p : DeFi.AMM.Params) {Ω : Type*}
    (u : ℕ → Ω → Trade) (s0 : Ω → DeFi.AMM.State) (n : ℕ) : Ω → ℝ :=
  logPortfolioReturnSeq (Ω := Ω) (Asset := Bool) w (ammReturn p u s0) n

theorem wealthAMM_log_growth_ae_tendsto_of_strongLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (W0 : ℝ) (w : Bool → ℝ) (p : DeFi.AMM.Params) (u : ℕ → Ω → Trade) (s0 : Ω → DeFi.AMM.State)
    (hW0 : 0 < W0)
    (hpos :
      ∀ᵐ ω ∂μ, ∀ n,
        0 < returnFactor (Ω := Ω) 1 (portfolioReturn (Asset := Bool) w (ammReturn p u s0)) n ω)
    (hint : Integrable (logAMMReturnSeq (Ω := Ω) w p u s0 0) μ)
    (hindep :
      Pairwise fun i j : ℕ =>
        IndepFun (logAMMReturnSeq (Ω := Ω) w p u s0 i)
          (logAMMReturnSeq (Ω := Ω) w p u s0 j) μ)
    (hident :
      ∀ i,
        IdentDistrib (logAMMReturnSeq (Ω := Ω) w p u s0 i)
          (logAMMReturnSeq (Ω := Ω) w p u s0 0) μ μ) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ =>
          (Real.log (wealthAMM (Ω := Ω) W0 w p u s0 n ω) - Real.log W0) / n)
        atTop (𝓝 μ[logAMMReturnSeq (Ω := Ω) w p u s0 0]) := by
  simpa [wealthAMM, logAMMReturnSeq, wealthPortfolio, logPortfolioReturnSeq] using
    (wealthPortfolio_log_growth_ae_tendsto_of_strongLaw (Ω := Ω) (μ := μ)
      (Asset := Bool) (W0 := W0) (w := w) (R := ammReturn p u s0) hW0 hpos hint hindep hident)

end DeFiAMM

end

end Kelly
end Economics
end HeytingLean
