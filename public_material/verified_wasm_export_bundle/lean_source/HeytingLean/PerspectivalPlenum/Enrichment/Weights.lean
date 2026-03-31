import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Real.Basic

namespace HeytingLean
namespace PerspectivalPlenum
namespace Enrichment

universe u v

/-- A semiring-valued weighting on an index type. -/
structure Weighting (ι : Type u) (W : Type v) [Semiring W] where
  weight : ι → W

namespace Weighting

variable {ι : Type u} {W : Type v} [Semiring W]

/-- Pointwise product of two weightings. -/
def mul (A B : Weighting ι W) : Weighting ι W :=
  { weight := fun i => A.weight i * B.weight i }

/-- Pointwise sum of two weightings. -/
def add (A B : Weighting ι W) : Weighting ι W :=
  { weight := fun i => A.weight i + B.weight i }

@[simp] theorem mul_apply (A B : Weighting ι W) (i : ι) :
    (mul A B).weight i = A.weight i * B.weight i := rfl

@[simp] theorem add_apply (A B : Weighting ι W) (i : ι) :
    (add A B).weight i = A.weight i + B.weight i := rfl

end Weighting

/-- Probability-flavored scalar with explicit `[0,1]` bounds. -/
structure ProbWeight where
  val : ℝ
  nonneg : 0 ≤ val
  le_one : val ≤ 1

instance : Coe ProbWeight ℝ where
  coe p := p.val

@[simp] theorem probWeight_nonneg (p : ProbWeight) : (0 : ℝ) ≤ p :=
  p.nonneg

@[simp] theorem probWeight_le_one (p : ProbWeight) : (p : ℝ) ≤ 1 :=
  p.le_one

/-- Certain weight (`1`). -/
def certain : ProbWeight :=
  { val := 1
    nonneg := zero_le_one
    le_one := le_rfl }

/-- Impossible weight (`0`). -/
def impossible : ProbWeight :=
  { val := 0
    nonneg := le_rfl
    le_one := zero_le_one }

@[simp] theorem certain_val : ((certain : ProbWeight) : ℝ) = 1 := rfl
@[simp] theorem impossible_val : ((impossible : ProbWeight) : ℝ) = 0 := rfl

end Enrichment
end PerspectivalPlenum
end HeytingLean
