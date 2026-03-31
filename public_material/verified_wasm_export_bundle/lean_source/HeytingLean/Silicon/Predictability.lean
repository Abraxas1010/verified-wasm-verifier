import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Finset.Lattice.Fold
import HeytingLean.Silicon.Leakage

namespace HeytingLean
namespace Silicon

noncomputable section

open scoped BigOperators

open HeytingLean.Probability.InfoTheory

universe u

namespace Predictability

variable {X Y : Type u} [Fintype X] [Fintype Y]

/-- Accuracy of a predictor `g : X → Y` under a joint distribution `P_{X,Y}`. -/
noncomputable def accuracy [DecidableEq Y] (P : Run X Y) (g : X → Y) : ℝ :=
  FinDist.probEvent P (fun xy => g xy.1 = xy.2)

theorem accuracy_prod [DecidableEq Y] (PX : FinDist X) (PY : FinDist Y) (g : X → Y) :
    accuracy (X := X) (Y := Y) (P := FinDist.prod PX PY) g = ∑ x : X, PX.pmf x * PY.pmf (g x) := by
  classical
  unfold accuracy
  -- Expand `probEvent` and the product pmf, then separate the sum over `X × Y`.
  rw [FinDist.probEvent_eq_sum (P := FinDist.prod PX PY) (E := fun xy : X × Y => g xy.1 = xy.2)]
  have hsplit :
      (∑ xy : X × Y, if g xy.1 = xy.2 then PX.pmf xy.1 * PY.pmf xy.2 else 0) =
        ∑ x : X, ∑ y : Y, if g x = y then PX.pmf x * PY.pmf y else 0 := by
    simpa using
      (Fintype.sum_prod_type (fun xy : X × Y => if g xy.1 = xy.2 then PX.pmf xy.1 * PY.pmf xy.2 else 0))
  -- Evaluate the inner sum using `Fintype.sum_ite_eq`.
  calc
    (∑ xy : X × Y, if g xy.1 = xy.2 then (FinDist.prod PX PY).pmf xy else 0)
        = ∑ xy : X × Y, if g xy.1 = xy.2 then PX.pmf xy.1 * PY.pmf xy.2 else 0 := by
            simp [FinDist.prod]
    _ = ∑ x : X, ∑ y : Y, if g x = y then PX.pmf x * PY.pmf y else 0 := hsplit
    _ = ∑ x : X, PX.pmf x * PY.pmf (g x) := by
          refine Fintype.sum_congr (fun x : X => ∑ y : Y, if g x = y then PX.pmf x * PY.pmf y else 0)
            (fun x : X => PX.pmf x * PY.pmf (g x)) ?_
          intro x
          simp

/-- Maximum point mass `max_y Q(y)` of a finite distribution. -/
noncomputable def maxMass (Q : FinDist Y) [Nonempty Y] : ℝ :=
  (Finset.univ : Finset Y).sup' (by simp) Q.pmf

theorem maxMass_congr {Q : FinDist Y} [Nonempty Y] {H₁ H₂ : (Finset.univ : Finset Y).Nonempty} :
    (Finset.univ : Finset Y).sup' H₁ Q.pmf = (Finset.univ : Finset Y).sup' H₂ Q.pmf := by
  cases Subsingleton.elim H₁ H₂
  rfl

theorem pmf_le_maxMass (Q : FinDist Y) [Nonempty Y] (y : Y) : Q.pmf y ≤ maxMass (Y := Y) Q := by
  classical
  have h' :
      Q.pmf y ≤ (Finset.univ : Finset Y).sup' ⟨y, by simp⟩ Q.pmf := by
    simpa using (Finset.le_sup' (s := (Finset.univ : Finset Y)) (f := Q.pmf) (b := y) (by simp))
  have huniv : (Finset.univ : Finset Y).Nonempty :=
    by simp
  have hcongr :
      (Finset.univ : Finset Y).sup' ⟨y, by simp⟩ Q.pmf =
        (Finset.univ : Finset Y).sup' huniv Q.pmf :=
    maxMass_congr (Y := Y) (Q := Q) (H₁ := ⟨y, by simp⟩) (H₂ := huniv)
  simpa [maxMass, huniv, hcongr] using h'

/-- Baseline accuracy of the best constant predictor, `max_y P_Y(y)`. -/
noncomputable def baseline [Nonempty Y] (P : Run X Y) : ℝ :=
  maxMass (Y := Y) (Run.obsMarginal (S := X) (O := Y) P)

theorem accuracy_le_baseline_of_independent [DecidableEq Y] [Nonempty Y]
    (P : Run X Y) (h : Independent (S := X) (O := Y) P) (g : X → Y) :
    accuracy (X := X) (Y := Y) P g ≤ baseline (X := X) (Y := Y) P := by
  classical
  rcases h with ⟨PX, PY, rfl⟩
  -- Reduce to a bound under a product distribution.
  have hacc :
      accuracy (X := X) (Y := Y) (P := FinDist.prod PX PY) g ≤ maxMass (Y := Y) PY := by
    -- Expand `accuracy` to a weighted average of `PY` values and bound it by the maximum mass.
    rw [accuracy_prod (X := X) (Y := Y) (PX := PX) (PY := PY) (g := g)]
    have hpoint : ∀ x : X, PY.pmf (g x) ≤ maxMass (Y := Y) PY := by
      intro x
      exact pmf_le_maxMass (Y := Y) (Q := PY) (y := g x)
    have hterm : ∀ x : X, PX.pmf x * PY.pmf (g x) ≤ PX.pmf x * maxMass (Y := Y) PY := by
      intro x
      exact mul_le_mul_of_nonneg_left (hpoint x) (PX.nonneg x)
    have hsum :
        (∑ x : X, PX.pmf x * PY.pmf (g x)) ≤ ∑ x : X, PX.pmf x * maxMass (Y := Y) PY := by
      classical
      -- Rewrite `Fintype.sum` as a `Finset.univ` sum and apply `Finset.sum_le_sum`.
      simpa using
        (Finset.sum_le_sum (s := (Finset.univ : Finset X)) (fun x _hx => hterm x))
    have hsum' :
        (∑ x : X, PX.pmf x * maxMass (Y := Y) PY) = maxMass (Y := Y) PY := by
      classical
      calc
        (∑ x : X, PX.pmf x * maxMass (Y := Y) PY)
            = (∑ x : X, PX.pmf x) * maxMass (Y := Y) PY := by
                simpa using
                  (Finset.sum_mul (s := (Finset.univ : Finset X)) (f := fun x : X => PX.pmf x)
                    (a := maxMass (Y := Y) PY)).symm
        _ = maxMass (Y := Y) PY := by simp [PX.sum_one]
    exact (le_trans hsum (le_of_eq hsum'))
  -- Rewrite the `baseline` of a product distribution as `maxMass PY`.
  have hR :
      Run.obsMarginal (S := X) (O := Y) (FinDist.prod PX PY) = PY :=
    FinDistLemmas.marginalRight_prod (α := X) (β := Y) PX PY
  simpa [baseline, hR] using hacc

theorem not_independent_of_accuracy_gt_baseline [DecidableEq Y] [Nonempty Y]
    (P : Run X Y) (g : X → Y) (hgt : baseline (X := X) (Y := Y) P < accuracy (X := X) (Y := Y) P g) :
    ¬ Independent (S := X) (O := Y) P := by
  intro hind
  have hle := accuracy_le_baseline_of_independent (X := X) (Y := Y) (P := P) hind g
  have : baseline (X := X) (Y := Y) P < baseline (X := X) (Y := Y) P :=
    lt_of_lt_of_le hgt hle
  exact lt_irrefl _ this

end Predictability

end

end Silicon
end HeytingLean
