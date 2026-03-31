import HeytingLean.Representations.Matrix.Projection

/-!
# Eigenforms (eigenvalue 1) for matrices

For projection matrices, the fixed space coincides with the eigenspace for eigenvalue `1`.
We package this as a small, proof-friendly lemma:

`P.mulVec v = v` iff `v ∈ range (toLin' P)` when `P` is idempotent.
-/

namespace HeytingLean
namespace Representations
namespace Matrix

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]
variable {R : Type u} [CommRing R]

/-- An eigenform (for this paper) is a nonzero `v` with eigenvalue `1`. -/
def IsEigenform (P : Matrix n n R) (v : n → R) : Prop :=
  P.mulVec v = v ∧ v ≠ 0

/-- The eigenspace for eigenvalue `1` as a submodule.

We define it as the kernel of `P - 1` (as a linear map).
-/
def eigenspaceOne (P : Matrix n n R) : Submodule R (n → R) :=
  LinearMap.ker (Matrix.toLin' P - LinearMap.id)

theorem mem_eigenspaceOne_iff (P : Matrix n n R) (v : n → R) :
    v ∈ eigenspaceOne (R := R) P ↔ P.mulVec v = v := by
  -- unfold the kernel condition
  simp [eigenspaceOne, LinearMap.sub_apply, Matrix.toLin'_apply, sub_eq_zero]

theorem fixedSpace_eq_eigenspaceOne {P : Matrix n n R} (hP : IsProjection (P := P)) :
    fixedSpace (R := R) P = eigenspaceOne (R := R) P := by
  ext v
  constructor
  · intro hv
    -- Range → fixed point by idempotence.
    have hvfix : P.mulVec v = v := fixed_of_mem_fixedSpace (R := R) hP hv
    exact (mem_eigenspaceOne_iff (R := R) P v).2 hvfix
  · intro hv
    -- Fixed point → range because `v = P.mulVec v`.
    have hvfix : P.mulVec v = v := (mem_eigenspaceOne_iff (R := R) P v).1 hv
    refine ⟨v, ?_⟩
    -- `toLin' P v = P.mulVec v`.
    simp [Matrix.toLin'_apply, hvfix]

end Matrix
end Representations
end HeytingLean
