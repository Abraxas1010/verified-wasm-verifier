import Mathlib.Algebra.BigOperators.Ring.Finset
import HeytingLean.Probability.InfoTheory.FinDist
import HeytingLean.Silicon.Model

namespace HeytingLean
namespace Silicon

noncomputable section

open scoped BigOperators

open HeytingLean.Probability.InfoTheory

universe u

variable {S O : Type u} [Fintype S] [Fintype O]

/-- A (classical) stochastic channel from `S` to `O`. -/
abbrev Channel (S O : Type u) [Fintype S] [Fintype O] :=
  S → FinDist O

namespace Channel

/-- Build a joint distribution `P_{S,O}` from a prior `P_S` and a channel `P_{O|S}`. -/
noncomputable def joint (PS : FinDist S) (K : Channel S O) : Run S O where
  pmf so := PS.pmf so.1 * (K so.1).pmf so.2
  nonneg so := mul_nonneg (PS.nonneg _) ((K so.1).nonneg _)
  sum_one := by
    classical
    calc
      (∑ so : S × O, PS.pmf so.1 * (K so.1).pmf so.2)
          = ∑ s : S, ∑ o : O, PS.pmf s * (K s).pmf o := by
              simpa using
                (Fintype.sum_prod_type (fun so : S × O => PS.pmf so.1 * (K so.1).pmf so.2))
      _ = ∑ s : S, PS.pmf s * (∑ o : O, (K s).pmf o) := by
              simp [Finset.mul_sum]
      _ = ∑ s : S, PS.pmf s := by
              refine Fintype.sum_congr (fun s : S => PS.pmf s * (∑ o : O, (K s).pmf o)) (fun s : S => PS.pmf s) ?_
              intro s
              simp [(K s).sum_one]
      _ = 1 := by simpa using PS.sum_one

theorem stateMarginal_joint (PS : FinDist S) (K : Channel S O) :
    Run.stateMarginal (S := S) (O := O) (joint (S := S) (O := O) PS K) = PS := by
  classical
  ext s
  calc
    (Run.stateMarginal (S := S) (O := O) (joint (S := S) (O := O) PS K)).pmf s
        = ∑ o : O, (joint (S := S) (O := O) PS K).pmf (s, o) := by
            simp [Run.stateMarginal, FinDist.marginalLeft]
    _ = ∑ o : O, PS.pmf s * (K s).pmf o := by
            simp [joint]
    _ = PS.pmf s * (∑ o : O, (K s).pmf o) := by
            simpa using
              (Finset.mul_sum (s := (Finset.univ : Finset O)) (f := fun o : O => (K s).pmf o)
                (a := PS.pmf s)).symm
    _ = PS.pmf s := by
            simp [(K s).sum_one]

/-- The observable marginal of `joint PS K` is the mixture `o ↦ ∑ s, PS(s) * K(s)(o)`. -/
noncomputable def obsMixture (PS : FinDist S) (K : Channel S O) : FinDist O where
  pmf o := ∑ s : S, PS.pmf s * (K s).pmf o
  nonneg o := by
    classical
    refine Finset.sum_nonneg ?_
    intro s _hs
    exact mul_nonneg (PS.nonneg s) ((K s).nonneg o)
  sum_one := by
    classical
    calc
      (∑ o : O, ∑ s : S, PS.pmf s * (K s).pmf o)
          = ∑ s : S, ∑ o : O, PS.pmf s * (K s).pmf o := by
              -- Swap the finite sums.
              have h1 :
                  (∑ os : O × S, PS.pmf os.2 * (K os.2).pmf os.1) =
                    ∑ o : O, ∑ s : S, PS.pmf s * (K s).pmf o := by
                      simpa using
                        (Fintype.sum_prod_type (fun os : O × S => PS.pmf os.2 * (K os.2).pmf os.1))
              have h2 :
                  (∑ os : O × S, PS.pmf os.2 * (K os.2).pmf os.1) =
                    ∑ s : S, ∑ o : O, PS.pmf s * (K s).pmf o := by
                      simpa using
                        (Fintype.sum_prod_type_right (fun os : O × S => PS.pmf os.2 * (K os.2).pmf os.1))
              exact h1.symm.trans h2
      _ = ∑ s : S, PS.pmf s := by
              refine Fintype.sum_congr
                (fun s : S => ∑ o : O, PS.pmf s * (K s).pmf o)
                (fun s : S => PS.pmf s) ?_
              intro s
              calc
                (∑ o : O, PS.pmf s * (K s).pmf o)
                    = PS.pmf s * (∑ o : O, (K s).pmf o) := by
                        simp [Finset.mul_sum]
                _ = PS.pmf s := by simp [(K s).sum_one]
      _ = 1 := by simpa using PS.sum_one

theorem obsMarginal_joint (PS : FinDist S) (K : Channel S O) :
    Run.obsMarginal (S := S) (O := O) (joint (S := S) (O := O) PS K) = obsMixture (S := S) (O := O) PS K := by
  classical
  ext o
  calc
    (Run.obsMarginal (S := S) (O := O) (joint (S := S) (O := O) PS K)).pmf o
        = ∑ s : S, (joint (S := S) (O := O) PS K).pmf (s, o) := by
            simp [Run.obsMarginal, FinDist.marginalRight]
    _ = ∑ s : S, PS.pmf s * (K s).pmf o := by
            simp [joint]
    _ = (obsMixture (S := S) (O := O) PS K).pmf o := by
            simp [obsMixture]

end Channel

end

end Silicon
end HeytingLean
