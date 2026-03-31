import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import HeytingLean.Crypto.Quantum.Bell.CHSH.Correlations

/-!
# Quantum correlators (vector strategy model)

We model a "quantum" CHSH strategy by unit vectors `a0,a1,b0,b1` in a real inner product space,
with correlators `E(x,y) = ⟪a_x, b_y⟫`.

This abstraction is enough to prove the `2 * sqrt 2` upper bound without importing density
matrices.
-/

namespace HeytingLean
namespace Crypto
namespace Quantum
namespace Bell
namespace Tsirelson

open HeytingLean.Crypto.Quantum.Bell.CHSH

universe u

/-- A vector strategy for CHSH: four unit vectors. -/
structure QuantumStrategy (V : Type u) [NormedAddCommGroup V] [InnerProductSpace Real V] where
  a0 : V
  a1 : V
  b0 : V
  b1 : V
  norm_a0 : norm a0 = 1
  norm_a1 : norm a1 = 1
  norm_b0 : norm b0 = 1
  norm_b1 : norm b1 = 1

namespace QuantumStrategy

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace Real V] (S : QuantumStrategy V)

/-- Alice's vector for setting `x`. -/
def aVec (x : Setting) : V := if x then S.a1 else S.a0

/-- Bob's vector for setting `y`. -/
def bVec (y : Setting) : V := if y then S.b1 else S.b0

/-- Correlator induced by a vector strategy. -/
def toCorrelator : Correlator where
  E := fun x y => inner Real (S.aVec x) (S.bVec y)
  bounded := by
    intro x y
    have ha : norm (S.aVec x) = 1 := by
      by_cases hx : x
      · simp [QuantumStrategy.aVec, hx, S.norm_a1]
      · simp [QuantumStrategy.aVec, hx, S.norm_a0]
    have hb : norm (S.bVec y) = 1 := by
      by_cases hy : y
      · simp [QuantumStrategy.bVec, hy, S.norm_b1]
      · simp [QuantumStrategy.bVec, hy, S.norm_b0]
    have habs : |inner Real (S.aVec x) (S.bVec y)| ≤ (1 : Real) := by
      have hcs := abs_real_inner_le_norm (S.aVec x) (S.bVec y)
      nlinarith [hcs, ha, hb]
    simpa using (abs_le.mp habs)

end QuantumStrategy

end Tsirelson
end Bell
end Quantum
end Crypto
end HeytingLean

