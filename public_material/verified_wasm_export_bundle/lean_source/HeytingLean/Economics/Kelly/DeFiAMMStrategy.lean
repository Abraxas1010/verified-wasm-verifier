import HeytingLean.Economics.Kelly.DeFiAMM

namespace HeytingLean
namespace Economics
namespace Kelly

noncomputable section

open scoped BigOperators

open HeytingLean.DeFi

namespace DeFiAMM

/-- A stateful AMM trading strategy: at time `n`, given the current AMM
state and the environment `ω`, choose a trade action. -/
structure AMMStrategy (Ω : Type*) where
  policy : ℕ → DeFi.AMM.State → Ω → Trade

def stateSeqPolicy {Ω : Type*} (p : DeFi.AMM.Params) (π : ℕ → DeFi.AMM.State → Ω → Trade)
    (s0 : Ω → DeFi.AMM.State) : ℕ → Ω → DeFi.AMM.State :=
  fun n ω =>
    Nat.rec (s0 ω) (fun k st => applyTrade p st (π k st ω)) n

def tradeSeqFromPolicy {Ω : Type*} (p : DeFi.AMM.Params) (π : ℕ → DeFi.AMM.State → Ω → Trade)
    (s0 : Ω → DeFi.AMM.State) : ℕ → Ω → Trade :=
  fun n ω => π n (stateSeqPolicy p π s0 n ω) ω

@[simp] lemma stateSeqPolicy_zero {Ω : Type*} (p : DeFi.AMM.Params) (π : ℕ → DeFi.AMM.State → Ω → Trade)
    (s0 : Ω → DeFi.AMM.State) (ω : Ω) :
    stateSeqPolicy p π s0 0 ω = s0 ω := by
  simp [stateSeqPolicy]

lemma stateSeqPolicy_succ {Ω : Type*} (p : DeFi.AMM.Params) (π : ℕ → DeFi.AMM.State → Ω → Trade)
    (s0 : Ω → DeFi.AMM.State) (n : ℕ) (ω : Ω) :
    stateSeqPolicy p π s0 (n + 1) ω
      = applyTrade p (stateSeqPolicy p π s0 n ω) (π n (stateSeqPolicy p π s0 n ω) ω) := by
  simp [stateSeqPolicy]

lemma stateSeq_eq_stateSeqPolicy {Ω : Type*} (p : DeFi.AMM.Params) (π : ℕ → DeFi.AMM.State → Ω → Trade)
    (s0 : Ω → DeFi.AMM.State) :
    stateSeq p (tradeSeqFromPolicy p π s0) s0 = stateSeqPolicy p π s0 := by
  funext n ω
  induction n with
  | zero =>
      simp [stateSeq, stateSeqPolicy, tradeSeqFromPolicy]
  | succ n ih =>
      have hrec :=
        (stateSeq_succ (p := p) (u := tradeSeqFromPolicy p π s0) (s0 := s0) (n := n) (ω := ω))
      -- unfold both recurrences at `n+1`
      simp [hrec, tradeSeqFromPolicy, stateSeqPolicy_succ, ih]

end DeFiAMM

end

end Kelly
end Economics
end HeytingLean
