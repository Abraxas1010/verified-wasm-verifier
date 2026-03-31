import HeytingLean.Metrics.Magnitude.Basic
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Data.Fintype.BigOperators

namespace HeytingLean
namespace Metrics
namespace Magnitude

/-- A finite similarity datum with integer-valued kernel. -/
structure SimilarityData (α : Type*) [Fintype α] [DecidableEq α] where
  sim : α → α → ℤ
  sim_self : ∀ x, sim x x = 1
  sim_symm : ∀ x y, sim x y = sim y x

/-- Magnitude weighting equation: `Σ_j sim(i,j)·w(j) = 1` for each `i`. -/
def IsMagnitudeWeighting {α : Type*} [Fintype α] [DecidableEq α]
    (S : SimilarityData α) (w : α → ℤ) : Prop :=
  ∀ i, Finset.sum Finset.univ (fun j => S.sim i j * w j) = 1

/-- Aggregate magnitude induced by a weighting. -/
def magnitudeOfWeighting {α : Type*} [Fintype α] (w : α → ℤ) : ℤ :=
  Finset.sum Finset.univ w

/-- Discrete similarity kernel (`1` on diagonal, `0` off-diagonal). -/
def discreteSimilarity (α : Type*) [Fintype α] [DecidableEq α] : SimilarityData α where
  sim := fun x y => if x = y then 1 else 0
  sim_self := by intro x; simp
  sim_symm := by intro x y; simp [eq_comm]

/-- Uniform candidate weighting. -/
def uniformWeighting (α : Type*) : α → ℤ := fun _ => 1

/-- Uniform weighting solves the discrete similarity equations. -/
theorem uniformWeighting_is_discrete_weighting (α : Type*) [Fintype α] [DecidableEq α] :
    IsMagnitudeWeighting (discreteSimilarity α) (uniformWeighting α) := by
  unfold IsMagnitudeWeighting
  intro i
  classical
  calc
    Finset.sum Finset.univ
        (fun j => (discreteSimilarity α).sim i j * uniformWeighting α j)
        = Finset.sum Finset.univ (fun j => if i = j then (1 : ℤ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          by_cases hij : i = j
          · simp [discreteSimilarity, uniformWeighting, hij]
          · simp [discreteSimilarity, uniformWeighting, hij]
    _ = 1 := by
      simp

/-- Uniform weighting magnitude recovers finite cardinality. -/
theorem magnitudeOfWeighting_uniform (α : Type*) [Fintype α] :
    magnitudeOfWeighting (uniformWeighting α) = Int.ofNat (Fintype.card α) := by
  classical
  simp [magnitudeOfWeighting, uniformWeighting]

/-- Fixed-point operator associated to the weighting equation. -/
def weightingFixedPtOp {α : Type*} [Fintype α] [DecidableEq α]
    (S : SimilarityData α) : (α → ℤ) → (α → ℤ) :=
  fun w i => w i + 1 - Finset.sum Finset.univ (fun j => S.sim i j * w j)

/-- Weighting equations are equivalent to fixed-point equations for `weightingFixedPtOp`. -/
theorem magnitude_weighting_iff_fixedPt {α : Type*} [Fintype α] [DecidableEq α]
    (S : SimilarityData α) (w : α → ℤ) :
    IsMagnitudeWeighting S w ↔ Function.IsFixedPt (weightingFixedPtOp S) w := by
  constructor
  · intro hw
    unfold IsMagnitudeWeighting at hw
    funext i
    simp [weightingFixedPtOp, hw i]
  · intro hfix
    unfold IsMagnitudeWeighting
    intro i
    have hi := congrArg (fun f => f i) hfix
    change w i + 1 - Finset.sum Finset.univ (fun j => S.sim i j * w j) = w i at hi
    have hi' : w i + 1 = w i + Finset.sum Finset.univ (fun j => S.sim i j * w j) := by
      exact Int.sub_eq_iff_eq_add.mp hi
    have hs : (1 : ℤ) = Finset.sum Finset.univ (fun j => S.sim i j * w j) :=
      Int.add_left_cancel hi'
    exact hs.symm

/-- For discrete similarity, the uniform weighting is a fixed point of the
associated weighting operator. -/
theorem uniformWeighting_fixedPt_discrete (α : Type*) [Fintype α] [DecidableEq α] :
    Function.IsFixedPt (weightingFixedPtOp (discreteSimilarity α)) (uniformWeighting α) := by
  exact (magnitude_weighting_iff_fixedPt
    (S := discreteSimilarity α) (w := uniformWeighting α)).1
      (uniformWeighting_is_discrete_weighting α)

end Magnitude
end Metrics
end HeytingLean
