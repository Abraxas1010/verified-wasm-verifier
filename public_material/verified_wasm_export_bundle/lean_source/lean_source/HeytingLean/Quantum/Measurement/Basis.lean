import HeytingLean.Quantum.QState

/-!
Computational-basis measurement for finite-dimensional density matrices.

This is a deliberately small “thin layer” that we can prove correct using only:
- the existing `HeytingLean.Quantum.Density` API, and
- elementary Mathlib facts about matrix trace and `mulVec`.

It is enough to expose a physically meaningful, executable-friendly interface
(Born probabilities in the standard basis) without depending on external
quantum-info libraries.
-/

noncomputable section

namespace HeytingLean
namespace Quantum

open Matrix Complex
open scoped BigOperators

variable {n : ℕ}

/-- Born probability of observing basis state `i` when measuring `ρ` in the computational basis. -/
def basisProb (ρ : Density n) (i : Fin n) : ℝ :=
  (ρ.mat i i).re

@[simp] lemma basisProb_def (ρ : Density n) (i : Fin n) :
    basisProb ρ i = (ρ.mat i i).re := rfl

lemma basisProb_nonneg (ρ : Density n) (i : Fin n) : 0 ≤ basisProb ρ i := by
  classical
  have h := ρ.posSemidef (basisKet (n := n) i)
  -- `PosSemidef` on the basis ket gives nonnegativity of the corresponding diagonal entry.
  simpa [basisProb, inner_basis_mulVec] using h

lemma basisProb_sum (ρ : Density n) : (∑ i : Fin n, basisProb ρ i) = 1 := by
  classical
  -- `re (trace ρ) = sum (re diag)` by additivity of `Complex.re`.
  have hre :
      (Matrix.trace ρ.mat).re = ∑ i : Fin n, (ρ.mat i i).re := by
    -- Expand the trace and apply additivity of `Complex.re` expressed as an `AddMonoidHom`.
    unfold Matrix.trace
    -- Definitional reduction turns `Complex.reAddGroupHom` into `.re`.
    exact map_sum Complex.reAddGroupHom (fun i : Fin n => ρ.mat i i) Finset.univ
  -- Finish using `traceOne`.
  have : (∑ i : Fin n, (ρ.mat i i).re) = (Matrix.trace ρ.mat).re :=
    hre.symm
  calc
    (∑ i : Fin n, basisProb ρ i) = ∑ i : Fin n, (ρ.mat i i).re := by
      simp [basisProb]
    _ = (Matrix.trace ρ.mat).re := this
    _ = 1 := by
      simpa using Density.realTrace_eq_one ρ

end Quantum
end HeytingLean
