import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import HeytingLean.Epiplexity.Prelude
import HeytingLean.Security.Model.Computational

namespace HeytingLean
namespace Epiplexity
namespace Crypto

open scoped BigOperators

noncomputable section

open HeytingLean.Probability.InfoTheory
open HeytingLean.Security.Model.Computational

namespace BitStr

instance (n : Nat) : Nonempty (BitStr n) := by
  refine ⟨⟨0, ?_⟩⟩
  exact Nat.pow_pos (a := 2) (n := n) (Nat.succ_pos 1)

end BitStr

namespace FinDist

/-- Pushforward of a finite distribution along a function. -/
noncomputable def map {α β : Type u} [Fintype α] [Fintype β] (f : α → β) (P : FinDist α) :
    FinDist β := by
  classical
  refine
    { pmf := fun b => ∑ a : α, if f a = b then P.pmf a else 0
      nonneg := ?_
      sum_one := ?_ }
  · intro b
    refine Finset.sum_nonneg ?_
    intro a _
    by_cases h : f a = b <;> simp [h, P.nonneg a]
  · -- Sum over all outputs, then swap sums.
    have hswap :
        (∑ b : β, ∑ a : α, if f a = b then P.pmf a else 0)
          = ∑ a : α, ∑ b : β, if f a = b then P.pmf a else 0 := by
      -- Both sides are the sum over `β × α`.
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
              (fun a : α => ?_)
            · simp
      _ = 1 := by
            simpa using P.sum_one

end FinDist

/-!
Security predicates (assumption layer).

These are *Props* packaging the usual computational indistinguishability-style hypotheses on finite
probability spaces, without committing to a particular PPT/universal-machine model.
-/

/-- Probability that a distinguisher outputs `true` on samples from `P`. -/
noncomputable def probTrue {α : Type u} [Fintype α] (P : FinDist α) (D : α → Bool) : ℝ :=
  ∑ a : α, P.pmf a * (if D a then 1 else 0)

/-- Distinguishing advantage between distributions `P` and `Q` for a Boolean test. -/
noncomputable def advantage {α : Type u} [Fintype α] (P Q : FinDist α) (D : α → Bool) : ℝ :=
  |probTrue P D - probTrue Q D|

/-- A minimal distinguisher wrapper (tracked only by a time budget). -/
structure Distinguisher (α : Type u) where
  run : α → Bool
  runtime : Nat

namespace Distinguisher

instance {α : Type u} : CoeFun (Distinguisher α) (fun _ => α → Bool) :=
  ⟨fun D => D.run⟩

end Distinguisher

/-- Definition 3 (CSPRNG), as a finite indistinguishability predicate with advantage bound `ε(k)`. -/
def CSPRNGSecure (k n T : Nat) (G : BitStr k → BitStr n) (ε : Nat → ℝ) : Prop :=
  ∀ D : Distinguisher (BitStr n),
    D.runtime ≤ T →
      advantage
          (FinDist.map G (Epiplexity.FinDist.uniform (α := BitStr k)))
          (Epiplexity.FinDist.uniform (α := BitStr n))
          D.run
        ≤ ε k

/-- A minimal inverter wrapper (tracked only by a time budget). -/
structure Inverter (α β : Type u) where
  run : β → α
  runtime : Nat

namespace Inverter

instance {α β : Type u} : CoeFun (Inverter α β) (fun _ => β → α) :=
  ⟨fun A => A.run⟩

end Inverter

/-- Success probability of an inverter against `f`, sampling `x` uniformly. -/
noncomputable def owfSuccess {α β : Type u} [Fintype α] [Nonempty α] [DecidableEq β]
    (f : α → β) (A : Inverter α β) : ℝ :=
  let U : FinDist α := Epiplexity.FinDist.uniform (α := α)
  ∑ x : α, U.pmf x * (if f (A.run (f x)) = f x then 1 else 0)

/-- Definition 4 (OWF), as a finite inversion-success bound `≤ ε(n)` under a time budget. -/
def OWFSecure (α β : Type u) [Fintype α] [Nonempty α] [Fintype β] [DecidableEq β]
    (T : Nat) (f : α → β) (ε : Nat → ℝ) : Prop :=
  ∀ A : Inverter α β, A.runtime ≤ T → owfSuccess (f := f) A ≤ ε (Fintype.card α)

/-- Definition 20 (PRF), modeled as indistinguishability of a random keyed function vs a uniform random function. -/
def PRFSecure (k n m T : Nat) (F : BitStr k → BitStr n → BitStr m) (ε : Nat → ℝ) : Prop :=
  ∀ D : Distinguisher (BitStr n → BitStr m),
    D.runtime ≤ T →
      advantage
          (FinDist.map (fun key => F key) (Epiplexity.FinDist.uniform (α := BitStr k)))
          (Epiplexity.FinDist.uniform (α := (BitStr n → BitStr m)))
          D.run
        ≤ ε k

end

end Crypto
end Epiplexity
end HeytingLean
