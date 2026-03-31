import HeytingLean.Representations.Matrix.Core
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Matrix projections

This file introduces projection (idempotent) matrices and basic facts used by the
“nucleus-as-projection” narrative.

The main executable lemma here is: if `P^2 = P`, then every vector in the range of `P`
is fixed by `P`.
-/

namespace HeytingLean
namespace Representations
namespace Matrix

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]
variable {R : Type u} [CommSemiring R]

/-- A projection matrix satisfies `P * P = P`. -/
def IsProjection (P : Matrix n n R) : Prop :=
  P * P = P

/-- The fixed space (image) of a matrix, as a submodule. -/
def fixedSpace (P : Matrix n n R) : Submodule R (n → R) :=
  LinearMap.range (Matrix.toLin' P)

theorem mem_fixedSpace_of_mulVec_eq (P : Matrix n n R) {v : n → R} (hv : P.mulVec v = v) :
    v ∈ fixedSpace (R := R) P := by
  refine ⟨v, ?_⟩
  simpa [fixedSpace, Matrix.toLin'_apply] using hv

theorem fixed_of_mem_fixedSpace {P : Matrix n n R} (hP : IsProjection (P := P))
    {v : n → R} (hv : v ∈ fixedSpace (R := R) P) :
    P.mulVec v = v := by
  rcases hv with ⟨w, rfl⟩
  -- `v = P.mulVec w`; apply idempotence.
  have hidem : (P * P).mulVec w = P.mulVec w := by
    simpa using congrArg (fun Q => Q.mulVec w) hP
  have hmul : P.mulVec (P.mulVec w) = (P * P).mulVec w :=
    (Matrix.mulVec_mulVec (v := w) (M := P) (N := P))
  have : P.mulVec (P.mulVec w) = P.mulVec w := by
    exact hmul.trans hidem
  simpa [Matrix.toLin'_apply] using this

namespace IsProjection

omit [DecidableEq n] in
theorem mulVec_idempotent {P : Matrix n n R} (hP : IsProjection (P := P)) (v : n → R) :
    P.mulVec (P.mulVec v) = P.mulVec v := by
  have hidem : (P * P).mulVec v = P.mulVec v := by
    simpa using congrArg (fun Q => Q.mulVec v) hP
  have hmul : P.mulVec (P.mulVec v) = (P * P).mulVec v :=
    (Matrix.mulVec_mulVec (v := v) (M := P) (N := P))
  exact hmul.trans hidem

theorem mulVec_eq_of_mem_fixedSpace {P : Matrix n n R} (hP : IsProjection (P := P))
    {v : n → R} (hv : v ∈ fixedSpace (R := R) P) :
    P.mulVec v = v := by
  exact fixed_of_mem_fixedSpace (R := R) hP hv

theorem mem_fixedSpace_iff_mulVec_eq {P : Matrix n n R} (hP : IsProjection (P := P)) {v : n → R} :
    v ∈ fixedSpace (R := R) P ↔ P.mulVec v = v := by
  constructor
  · intro hv
    exact mulVec_eq_of_mem_fixedSpace (R := R) hP hv
  · intro hv
    exact mem_fixedSpace_of_mulVec_eq (R := R) P hv

end IsProjection

end Matrix
end Representations
end HeytingLean
