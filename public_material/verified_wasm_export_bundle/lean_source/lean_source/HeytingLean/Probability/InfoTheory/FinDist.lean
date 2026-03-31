import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import HeytingLean.Probability.InfoTheory.Core

namespace HeytingLean
namespace Probability
namespace InfoTheory

noncomputable section

open scoped BigOperators

/-!
`FinDist α` is a finitely-supported probability distribution on a `Fintype α`,
represented by a real-valued mass function.

This is a proof-first core used by the Shannon/Kelly development.
-/

structure FinDist (α : Type u) [Fintype α] where
  pmf : α → ℝ
  nonneg : ∀ a, 0 ≤ pmf a
  sum_one : (∑ a, pmf a) = 1

namespace FinDist

variable {α β : Type u} [Fintype α] [Fintype β]

@[ext] theorem ext (P Q : FinDist α) (h : ∀ a, P.pmf a = Q.pmf a) : P = Q := by
  cases P with
  | mk pmfP nonnegP sumP =>
    cases Q with
    | mk pmfQ nonnegQ sumQ =>
      have hpmf : pmfP = pmfQ := funext h
      subst hpmf
      have hnonneg : nonnegP = nonnegQ := Subsingleton.elim _ _
      have hsum : sumP = sumQ := Subsingleton.elim _ _
      cases hnonneg
      cases hsum
      rfl

def Pos (P : FinDist α) : Prop := ∀ a, 0 < P.pmf a

/-! ### Pushforward -/

/-- Pushforward of a finite distribution along a function. -/
noncomputable def map (f : α → β) (P : FinDist α) : FinDist β := by
  classical
  refine
    { pmf := fun b => ∑ a : α, if f a = b then P.pmf a else 0
      nonneg := ?_
      sum_one := ?_ }
  · intro b
    refine Finset.sum_nonneg ?_
    intro a _
    by_cases h : f a = b <;> simp [h, P.nonneg a]
  · have hswap :
        (∑ b : β, ∑ a : α, if f a = b then P.pmf a else 0)
          = ∑ a : α, ∑ b : β, if f a = b then P.pmf a else 0 := by
      have h1 :
          (∑ ba : β × α, if f ba.2 = ba.1 then P.pmf ba.2 else 0)
            = ∑ b : β, ∑ a : α, if f a = b then P.pmf a else 0 := by
        simpa using (Fintype.sum_prod_type
          (fun ba : β × α => if f ba.2 = ba.1 then P.pmf ba.2 else 0))
      have h2 :
          (∑ ba : β × α, if f ba.2 = ba.1 then P.pmf ba.2 else 0)
            = ∑ a : α, ∑ b : β, if f a = b then P.pmf a else 0 := by
        simpa using (Fintype.sum_prod_type_right
          (fun ba : β × α => if f ba.2 = ba.1 then P.pmf ba.2 else 0))
      exact h1.symm.trans h2
    calc
      (∑ b : β, ∑ a : α, if f a = b then P.pmf a else 0)
          = ∑ a : α, ∑ b : β, if f a = b then P.pmf a else 0 := hswap
      _ = ∑ a : α, P.pmf a := by
            refine Fintype.sum_congr
              (fun a : α => ∑ b : β, if f a = b then P.pmf a else 0)
              (fun a : α => P.pmf a)
              (fun a : α => by simp)
      _ = 1 := by simpa using P.sum_one

@[simp] theorem map_id (P : FinDist α) : map (f := fun a : α => a) P = P := by
  classical
  ext a
  simp [map]

/-! ### Expectation / event probability (finite-only) -/

/-- Expectation of a real-valued function under a finite distribution. -/
noncomputable def expect (P : FinDist α) (f : α → ℝ) : ℝ :=
  ∑ a : α, P.pmf a * f a

@[simp] theorem expect_const (P : FinDist α) (c : ℝ) : expect P (fun _ => c) = c := by
  classical
  unfold expect
  calc
    (∑ a : α, P.pmf a * (fun _ => c) a) = (∑ a : α, P.pmf a * c) := by simp
    _ = (∑ a : α, P.pmf a) * c := by
          simp [Finset.sum_mul]
    _ = c := by simp [P.sum_one]

theorem expect_add (P : FinDist α) (f g : α → ℝ) :
    expect P (fun a => f a + g a) = expect P f + expect P g := by
  classical
  unfold expect
  simp [mul_add, Finset.sum_add_distrib]

theorem expect_mul_const (P : FinDist α) (f : α → ℝ) (c : ℝ) :
    expect P (fun a => f a * c) = expect P f * c := by
  classical
  unfold expect
  simp [Finset.sum_mul, mul_assoc]

/-- Probability of an event `E` under `P`, expressed as an expectation of an indicator. -/
noncomputable def probEvent (P : FinDist α) (E : α → Prop) [DecidablePred E] : ℝ :=
  expect P (fun a => if E a then 1 else 0)

theorem probEvent_eq_sum (P : FinDist α) (E : α → Prop) [DecidablePred E] :
    probEvent P E = ∑ a : α, if E a then P.pmf a else 0 := by
  classical
  unfold probEvent expect
  simp [mul_ite]

theorem probEvent_nonneg (P : FinDist α) (E : α → Prop) [DecidablePred E] :
    0 ≤ probEvent P E := by
  classical
  rw [probEvent_eq_sum (P := P) (E := E)]
  refine Finset.sum_nonneg ?_
  intro a _
  by_cases h : E a <;> simp [h, P.nonneg a]

theorem probEvent_le_one (P : FinDist α) (E : α → Prop) [DecidablePred E] :
    probEvent P E ≤ 1 := by
  classical
  rw [probEvent_eq_sum (P := P) (E := E)]
  have hle : (∑ a : α, if E a then P.pmf a else 0) ≤ ∑ a : α, P.pmf a := by
    refine Finset.sum_le_sum ?_
    intro a _
    by_cases h : E a <;> simp [h, P.nonneg a]
  simpa [P.sum_one] using hle

def prod (P : FinDist α) (Q : FinDist β) : FinDist (α × β) where
  pmf ab := P.pmf ab.1 * Q.pmf ab.2
  nonneg ab := mul_nonneg (P.nonneg _) (Q.nonneg _)
  sum_one := by
    classical
    calc
      (∑ ab : α × β, P.pmf ab.1 * Q.pmf ab.2)
          = (∑ a : α, ∑ b : β, P.pmf a * Q.pmf b) := by
              simpa using (Fintype.sum_prod_type (fun ab : α × β => P.pmf ab.1 * Q.pmf ab.2))
      _ = (∑ a : α, P.pmf a * (∑ b : β, Q.pmf b)) := by
              simp [Finset.mul_sum]
      _ = (∑ a : α, P.pmf a) * (∑ b : β, Q.pmf b) := by
              simp [Finset.sum_mul]
      _ = 1 := by simp [P.sum_one, Q.sum_one]

def marginalLeft (P : FinDist (α × β)) : FinDist α where
  pmf a := ∑ b : β, P.pmf (a, b)
  nonneg a := by
    classical
    exact Finset.sum_nonneg (fun b _ => P.nonneg (a, b))
  sum_one := by
    classical
    have h :
        (∑ ab : α × β, P.pmf ab) = (∑ a : α, ∑ b : β, P.pmf (a, b)) := by
      simpa using (Fintype.sum_prod_type (fun ab : α × β => P.pmf ab))
    calc
      (∑ a : α, ∑ b : β, P.pmf (a, b))
          = (∑ ab : α × β, P.pmf ab) := by simpa using h.symm
      _ = 1 := P.sum_one

def marginalRight (P : FinDist (α × β)) : FinDist β where
  pmf b := ∑ a : α, P.pmf (a, b)
  nonneg b := by
    classical
    exact Finset.sum_nonneg (fun a _ => P.nonneg (a, b))
  sum_one := by
    classical
    have h :
        (∑ ab : α × β, P.pmf ab) = (∑ b : β, ∑ a : α, P.pmf (a, b)) := by
      simpa using (Fintype.sum_prod_type_right (fun ab : α × β => P.pmf ab))
    calc
      (∑ b : β, ∑ a : α, P.pmf (a, b))
          = (∑ ab : α × β, P.pmf ab) := by simpa using h.symm
      _ = 1 := P.sum_one

end FinDist

end

end InfoTheory
end Probability
end HeytingLean
