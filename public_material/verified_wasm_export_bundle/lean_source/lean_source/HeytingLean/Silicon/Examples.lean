import Mathlib.Tactic
import HeytingLean.Silicon.EarlyAbort
import HeytingLean.Silicon.Leakage
import HeytingLean.Silicon.Signature

namespace HeytingLean
namespace Silicon
namespace Examples

noncomputable section

open scoped BigOperators

open HeytingLean.Probability.InfoTheory

/-- Uniform distribution on `Bool`. -/
def unifBool : FinDist Bool where
  pmf := fun _ => (1 / 2 : ℝ)
  nonneg := by intro _; norm_num
  sum_one := by
    -- `∑ b : Bool, 1/2 = 1/2 + 1/2 = 1`.
    norm_num

/-- A deterministic distribution concentrating all mass on `true`. -/
def deltaTrue : FinDist Bool where
  pmf := fun b => if b then (1 : ℝ) else 0
  nonneg := by
    intro b
    by_cases hb : b <;> simp [hb]
  sum_one := by
    -- `P(true)=1`, `P(false)=0`.
    simp

example : Leakage (S := Bool) (O := Bool) (FinDist.prod unifBool unifBool) = 0 := by
  classical
  refine leakage_eq_zero_of_independent (S := Bool) (O := Bool) (P := FinDist.prod unifBool unifBool) ?_
  exact ⟨unifBool, unifBool, rfl⟩

example :
    ∃ a : Bool,
      FinDist.probEvent unifBool (fun x : Bool => x = a)
        ≠ FinDist.probEvent deltaTrue (fun x : Bool => x = a) := by
  classical
  have h : unifBool ≠ deltaTrue := by
    intro hEq
    have hpmf : (1 / 2 : ℝ) = (1 : ℝ) := by
      have hpmf' : unifBool.pmf true = deltaTrue.pmf true := by
        simp [hEq]
      simp [unifBool, deltaTrue] at hpmf'
    have hne : (1 / 2 : ℝ) ≠ (1 : ℝ) := by norm_num
    exact hne hpmf
  exact Signature.exists_singleton_prob_ne (α := Bool) (P := unifBool) (Q := deltaTrue) h

end

end Examples
end Silicon
end HeytingLean
