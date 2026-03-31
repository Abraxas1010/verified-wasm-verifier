import HeytingLean.Physics.String.PolyakovMVP

/-!
# String.PolyakovMVPSanity

Nontrivial compile-time checks for the Polyakov MVP (Path/Track B):
- conformal weight cancels for `Ω ≠ 0`,
- squared Frobenius form is invariant under a simple orthogonal `V` on the worldsheet side.
-/

namespace HeytingLean
namespace Tests
namespace String

open HeytingLean.Physics.String.PolyakovMVP

open scoped Matrix

namespace Examples

-- Worldsheet dimension fixed to 2 for this MVP.
abbrev WS := Fin 2
abbrev Target := Fin 3

def A : Matrix Target WS ℝ := fun
  | ⟨0, _⟩, ⟨0, _⟩ => 1
  | ⟨0, _⟩, ⟨1, _⟩ => 2
  | ⟨1, _⟩, ⟨0, _⟩ => 3
  | ⟨1, _⟩, ⟨1, _⟩ => 4
  | ⟨2, _⟩, ⟨0, _⟩ => 5
  | ⟨2, _⟩, ⟨1, _⟩ => 6

-- A simple orthogonal matrix on WS: swap coordinates (a permutation matrix).
def Vswap : Matrix WS WS ℝ := fun
  | ⟨0, _⟩, ⟨0, _⟩ => 0
  | ⟨0, _⟩, ⟨1, _⟩ => 1
  | ⟨1, _⟩, ⟨0, _⟩ => 1
  | ⟨1, _⟩, ⟨1, _⟩ => 0

theorem Vswap_mul_transpose : Vswap * Vswapᵀ = (1 : Matrix WS WS ℝ) := by
  classical
  -- brute force over Fin 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Vswap, Matrix.mul_apply]

theorem frob_invariant_swap :
    frobSq (m := Target) (n := WS) (A * Vswap) = frobSq (m := Target) (n := WS) A := by
  classical
  simpa using
    (frobSq_mul_right_invariant (n := WS) (k := Target) (A := A) (V := Vswap) Vswap_mul_transpose)

theorem conformal_cancels (Ω : ℝ) (hΩ : Ω ≠ 0) :
    conformalWeight Ω = (1 : ℝ) := by
  simpa using conformalWeight_eq_one (Ω := Ω) hΩ

end Examples

end String
end Tests
end HeytingLean
