import HeytingLean.Quantum.ActiveInference.CoreR
import HeytingLean.Quantum.ActiveInference.InfoR
import Mathlib.Tactic

/-
Compile-only sanity for Real-typed QAI (ProbVec-based).
-/

namespace HeytingLean
namespace Tests
namespace Quantum
namespace ActiveInference

open HeytingLean.Quantum.ActiveInference

def mR : DiscreteModelR :=
  let prior : Array ℝ := #[0.5, 0.5]
  let likeA0 : Array (Array ℝ) := #[#[0.8, 0.2], #[0.2, 0.8]]
  let likeA1 : Array (Array ℝ) := #[#[0.3, 0.7], #[0.7, 0.3]]
  { ns := 2, no := 2, na := 2, prior := prior, like := #[likeA0, likeA1] }

noncomputable def qR : Array ℝ := posteriorR mR 0 0
noncomputable def pOR : Array ℝ := predictObsR mR 0

/-- Diagonal KL nonnegativity sanity: KL(p‖p) ≥ 0 for a simple two-point distribution. -/
example : 0 ≤ klDivR #[0.5, 0.5] #[0.5, 0.5] :=
  klDivR_self_nonneg #[0.5, 0.5]

/-- Nontrivial KL nonnegativity sanity (2-point case): KL(p‖q) ≥ 0 under explicit
probability assumptions for a small two-point example. -/
example :
    0 ≤
      klDivR #[(0.25 : ℝ), (0.75 : ℝ)]
              #[(0.5 : ℝ), (0.5 : ℝ)] := by
  let p : Array ℝ := #[(0.25 : ℝ), (0.75 : ℝ)]
  let q : Array ℝ := #[(0.5 : ℝ), (0.5 : ℝ)]
  -- Nonnegativity of entries in p.
  have hp_nonneg :
      ∀ x ∈ p.toList, 0 ≤ x := by
    intro x hx
    have hx' : x = 0.25 ∨ x = 0.75 := by
      simpa [p] using hx
    cases hx' with
    | inl h =>
        subst h
        exact (by norm_num : 0 ≤ (0.25 : ℝ))
    | inr h =>
        subst h
        exact (by norm_num : 0 ≤ (0.75 : ℝ))
  -- Strict positivity of entries in q.
  have hq_pos :
      ∀ x ∈ q.toList, 0 < x := by
    intro x hx
    have hx' : x = 0.5 ∨ x = 0.5 := by
      simpa [q] using hx
    cases hx' with
    | inl h =>
        subst h
        exact (by norm_num : 0 < (0.5 : ℝ))
    | inr h =>
        subst h
        exact (by norm_num : 0 < (0.5 : ℝ))
  -- Lengths agree.
  have hlen :
      p.toList.length = q.toList.length := by
    simp [p, q]
  -- Both distributions sum to 1.
  have hp_sum1 :
      HeytingLean.Math.ProbVec.sumList p.toList = 1 := by
    have h :
        HeytingLean.Math.ProbVec.sumList p.toList =
          (0.25 + 0.75 : ℝ) := by
      simp [p, HeytingLean.Math.ProbVec.sumList]
    have h' : (0.25 + 0.75 : ℝ) = 1 := by
      norm_num
    exact h.trans h'
  have hq_sum1 :
      HeytingLean.Math.ProbVec.sumList q.toList = 1 := by
    have h :
        HeytingLean.Math.ProbVec.sumList q.toList =
          (0.5 + 0.5 : ℝ) := by
      simp [q, HeytingLean.Math.ProbVec.sumList]
    have h' : (0.5 + 0.5 : ℝ) = 1 := by
      norm_num
    exact h.trans h'
  -- Apply the general array-level Gibbs inequality.
  have h :
      0 ≤ klDivR p q :=
    klDivR_nonneg p q hp_nonneg hq_pos hlen hp_sum1 hq_sum1
  simpa [p, q] using h

/-- EFEInputs built from the Real-level posterior of `mR`, with
`post = prior`.  In this diagonal case, the information-gain term
`igR` is nonnegative via `igR_self_nonneg`. -/
noncomputable def efeDiagR : EFEInputs :=
  { costs := #[(0 : ℝ), (0 : ℝ)]
    post  := qR
    prior := qR }

example : 0 ≤ igR efeDiagR :=
  igR_self_nonneg efeDiagR rfl

/-- Nontrivial KL nonnegativity sanity (3-point case): KL(p‖q) ≥ 0 under
explicit probability assumptions for a small three-point example. -/
example :
    0 ≤
      klDivR #[(1/10 : ℝ), (3/10 : ℝ), (6/10 : ℝ)]
              #[(1/3 : ℝ),  (1/3 : ℝ),  (1/3 : ℝ)] := by
  let p : Array ℝ := #[(1/10 : ℝ), (3/10 : ℝ), (6/10 : ℝ)]
  let q : Array ℝ := #[(1/3 : ℝ), (1/3 : ℝ), (1/3 : ℝ)]
  -- Nonnegativity of entries in p.
  have hp_nonneg :
      ∀ x ∈ p.toList, 0 ≤ x := by
    intro x hx
    have hx' :
        x = (1/10 : ℝ) ∨ x = (3/10 : ℝ) ∨ x = (6/10 : ℝ) := by
      simpa [p] using hx
    cases hx' with
    | inl h =>
        subst h
        exact (by norm_num : 0 ≤ (1/10 : ℝ))
    | inr h' =>
        cases h' with
        | inl h =>
            subst h
            exact (by norm_num : 0 ≤ (3/10 : ℝ))
        | inr h =>
            subst h
            exact (by norm_num : 0 ≤ (6/10 : ℝ))
  -- Strict positivity of entries in q.
  have hq_pos :
      ∀ x ∈ q.toList, 0 < x := by
    intro x hx
    have hx' :
        x = (1/3 : ℝ) ∨ x = (1/3 : ℝ) ∨ x = (1/3 : ℝ) := by
      simpa [q] using hx
    cases hx' with
    | inl h =>
        subst h
        exact (by norm_num : 0 < (1/3 : ℝ))
    | inr h' =>
        cases h' with
        | inl h =>
            subst h
            exact (by norm_num : 0 < (1/3 : ℝ))
        | inr h =>
            subst h
            exact (by norm_num : 0 < (1/3 : ℝ))
  -- Lengths agree.
  have hlen :
      p.toList.length = q.toList.length := by
    simp [p, q]
  -- Both distributions sum to 1.
  have hp_sum1 :
      HeytingLean.Math.ProbVec.sumList p.toList = 1 := by
    have h :
        HeytingLean.Math.ProbVec.sumList p.toList =
          ((1/10 : ℝ) + (3/10 : ℝ) + (6/10 : ℝ)) := by
      -- sumList [1/10, 3/10, 6/10]
      simp [p, HeytingLean.Math.ProbVec.sumList, add_comm, add_left_comm, add_assoc]
    have h' :
        ((1/10 : ℝ) + (3/10 : ℝ) + (6/10 : ℝ)) = 1 := by
      norm_num
    exact h.trans h'
  have hq_sum1 :
      HeytingLean.Math.ProbVec.sumList q.toList = 1 := by
    have h :
        HeytingLean.Math.ProbVec.sumList q.toList =
          ((1/3 : ℝ) + (1/3 : ℝ) + (1/3 : ℝ)) := by
      -- sumList [1/3, 1/3, 1/3]
      simp [q, HeytingLean.Math.ProbVec.sumList, add_comm, add_left_comm, add_assoc]
    have h' :
        ((1/3 : ℝ) + (1/3 : ℝ) + (1/3 : ℝ)) = 1 := by
      norm_num
    exact h.trans h'
  -- Apply the general array-level Gibbs inequality.
  have h :
      0 ≤ klDivR p q :=
    klDivR_nonneg p q hp_nonneg hq_pos hlen hp_sum1 hq_sum1
  simpa [p, q] using h

/-- A nontrivial Real-level EFE example with distinct posterior and prior,
where `igR` is nonnegative by the Gibbs inequality and `efeR` therefore
dominates the risk term. -/
noncomputable def efeNontrivR : EFEInputs :=
  { costs := #[(1 : ℝ), (2 : ℝ)]
    post  := #[(0.25 : ℝ), (0.75 : ℝ)]
    prior := #[(0.5 : ℝ), (0.5 : ℝ)] }

lemma igR_efeNontrivR_nonneg : 0 ≤ igR efeNontrivR := by
  -- Probability assumptions for the 2-point posterior/prior used in `efeNontrivR`.
  let p : Array ℝ := efeNontrivR.post
  let q : Array ℝ := efeNontrivR.prior
  -- Nonnegativity of entries in p.
  have hp_nonneg :
      ∀ x ∈ p.toList, 0 ≤ x := by
    intro x hx
    have hx' : x = 0.25 ∨ x = 0.75 := by
      simpa [p, efeNontrivR] using hx
    cases hx' with
    | inl h =>
        subst h
        exact (by norm_num : 0 ≤ (0.25 : ℝ))
    | inr h =>
        subst h
        exact (by norm_num : 0 ≤ (0.75 : ℝ))
  -- Strict positivity of entries in q.
  have hq_pos :
      ∀ x ∈ q.toList, 0 < x := by
    intro x hx
    have hx' : x = 0.5 ∨ x = 0.5 := by
      simpa [q, efeNontrivR] using hx
    cases hx' with
    | inl h =>
        subst h
        exact (by norm_num : 0 < (0.5 : ℝ))
    | inr h =>
        subst h
        exact (by norm_num : 0 < (0.5 : ℝ))
  -- Lengths agree.
  have hlen :
      p.toList.length = q.toList.length := by
    simp [p, q, efeNontrivR]
  -- Both distributions sum to 1.
  have hp_sum1 :
      HeytingLean.Math.ProbVec.sumList p.toList = 1 := by
    have h :
        HeytingLean.Math.ProbVec.sumList p.toList =
          (0.25 + 0.75 : ℝ) := by
      simp [p, efeNontrivR, HeytingLean.Math.ProbVec.sumList]
    have h' : (0.25 + 0.75 : ℝ) = 1 := by
      norm_num
    exact h.trans h'
  have hq_sum1 :
      HeytingLean.Math.ProbVec.sumList q.toList = 1 := by
    have h :
        HeytingLean.Math.ProbVec.sumList q.toList =
          (0.5 + 0.5 : ℝ) := by
      simp [q, efeNontrivR, HeytingLean.Math.ProbVec.sumList]
    have h' : (0.5 + 0.5 : ℝ) = 1 := by
      norm_num
    exact h.trans h'
  -- Apply the array-level Gibbs inequality for KL.
  have hkl :
      0 ≤ klDivR p q :=
    klDivR_nonneg p q hp_nonneg hq_pos hlen hp_sum1 hq_sum1
  -- Unfold `igR` and specialise to this EFE input.
  unfold igR
  simpa [efeNontrivR] using hkl

example : 0 ≤ igR efeNontrivR :=
  igR_efeNontrivR_nonneg

example : riskR efeNontrivR ≤ efeR efeNontrivR :=
  riskR_le_efeR_of_igR_nonneg efeNontrivR igR_efeNontrivR_nonneg

end ActiveInference
end Quantum
end Tests
end HeytingLean
