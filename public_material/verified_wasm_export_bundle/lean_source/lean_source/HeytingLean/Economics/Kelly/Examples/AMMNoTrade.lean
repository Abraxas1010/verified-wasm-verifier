import HeytingLean.Economics.Kelly.DeFiAMMStrategy

namespace HeytingLean
namespace Economics
namespace Kelly

noncomputable section

open scoped BigOperators

open HeytingLean.DeFi

namespace DeFiAMM

def noopTrade : Trade := Trade.swapX 0

def noopSeq {Ω : Type*} : ℕ → Ω → Trade := fun _ _ => noopTrade

lemma swapX_zero_eq (p : DeFi.AMM.Params) (s : DeFi.AMM.State) (hx : s.x ≠ 0) :
    DeFi.AMM.swapX p s 0 = s := by
  cases s with
  | mk x y =>
      have hx' : (x : ℚ) ≠ 0 := hx
      have hcancel : (x * y) / x = y := by
        simpa [div_eq_mul_inv, mul_assoc] using (mul_div_cancel_left₀ (b := y) (a := x) hx')
      -- Expand the swap definition and use `k = x*y`.
      simp [DeFi.AMM.swapX, DeFi.AMM.effectiveInputX, DeFi.AMM.gamma, DeFi.AMM.k, hcancel]

lemma stateSeq_noop_eq {Ω : Type*} (p : DeFi.AMM.Params) (s0 : Ω → DeFi.AMM.State)
    (hx0 : ∀ ω, (s0 ω).x ≠ 0) :
    ∀ n ω, stateSeq p (noopSeq (Ω := Ω)) s0 n ω = s0 ω := by
  intro n
  induction n with
  | zero =>
      intro ω
      simp [stateSeq]
  | succ n ih =>
      intro ω
      have hprev : stateSeq p (noopSeq (Ω := Ω)) s0 n ω = s0 ω := ih ω
      -- unfold recurrence and simplify with the `swapX_zero_eq` lemma
      have hstep := stateSeq_succ (p := p) (u := noopSeq (Ω := Ω)) (s0 := s0) (n := n) (ω := ω)
      simp [hstep, noopSeq, noopTrade, applyTrade, hprev, swapX_zero_eq (p := p) (s := s0 ω)
        (hx := hx0 ω)]

lemma ammReturn_noop_eq_zero {Ω : Type*} (p : DeFi.AMM.Params) (s0 : Ω → DeFi.AMM.State)
    (hx0 : ∀ ω, (s0 ω).x ≠ 0) (hy0 : ∀ ω, (s0 ω).y ≠ 0) :
    ∀ n ω t, ammReturn p (noopSeq (Ω := Ω)) s0 n ω t = 0 := by
  intro n ω t
  have hs : ∀ m, stateSeq p (noopSeq (Ω := Ω)) s0 m ω = s0 ω := fun m =>
    stateSeq_noop_eq (Ω := Ω) p s0 hx0 m ω
  -- reduce to a division `a/a - 1` with `a ≠ 0`
  have hnonzero : reserveR t (s0 ω) ≠ 0 := by
    cases t <;> simp [reserveR, reserveQ, hx0 ω, hy0 ω]
  have : reserveR t (s0 ω) / reserveR t (s0 ω) - 1 = 0 := by
    simp [div_self hnonzero]
  simpa [ammReturn, hs, reserveR, reserveQ] using this

lemma wealthAMM_noop_eq {Ω : Type*} (W0 : ℝ) (w : Bool → ℝ) (p : DeFi.AMM.Params)
    (s0 : Ω → DeFi.AMM.State)
    (hx0 : ∀ ω, (s0 ω).x ≠ 0) (hy0 : ∀ ω, (s0 ω).y ≠ 0) :
    ∀ n ω, wealthAMM (Ω := Ω) W0 w p (noopSeq (Ω := Ω)) s0 n ω = W0 := by
  intro n ω
  have hR : ∀ m t, ammReturn p (noopSeq (Ω := Ω)) s0 m ω t = 0 :=
    fun m t => ammReturn_noop_eq_zero (Ω := Ω) p s0 hx0 hy0 m ω t
  -- `wealthAMM` is a product of `1 + portfolioReturn ...`; with zero returns this is constantly `W0`.
  simp [wealthAMM, wealthPortfolio, wealthR, portfolioReturn, returnFactor, hR]

end DeFiAMM

end

end Kelly
end Economics
end HeytingLean
