import HeytingLean.LoF.Nucleus
import HeytingLean.LoF.HeytingCore

/-!
# Boundary → Heyting (explicit packaging)

`WIP/unified_math.md` asserts that considering the “boundary” of a distinction yields
Heyting structure.

Formally, in this codebase:

* a re-entry nucleus `R : Reentry α` determines a fixed-point sublocale `Ω_R` (`R.Omega`),
* `R.Omega` carries a canonical `HeytingAlgebra` instance (see `LoF.HeytingCore`),
* the LoF nucleus development identifies a distinguished boundary object `R.eulerBoundary`
  (defined as the `sInf` of the nontrivial fixed points inside the support window).

This module is a small “glue” layer that *explicitly packages* these ingredients, so the
boundary story is not only implicit via imports.
-/

namespace HeytingLean
namespace LoF

namespace BoundaryHeyting

universe u

variable {α : Type u} [PrimaryAlgebra α]

open Reentry

/-- The boundary object singled out by the LoF nucleus theory. -/
noncomputable def boundary (R : Reentry α) : R.Omega :=
  R.eulerBoundary

@[simp] theorem boundary_def (R : Reentry α) : boundary (R := R) = R.eulerBoundary := rfl

/-- The Euler boundary is the least element of the boundary-candidate set. -/
theorem boundary_isLeast (R : Reentry α) : IsLeast (R.boundaryCandidates) (boundary (R := R)) := by
  simpa [boundary] using R.eulerBoundary_isLeast

/-- The Heyting structure on `Ω_R` (fixed points) is canonical. -/
instance (R : Reentry α) : HeytingAlgebra (R.Omega) := inferInstance

/-- A representative “Heyting-from-boundary” lemma: modus ponens inside `Ω_R`. -/
theorem boundary_modusPonens (R : Reentry α) (a b : R.Omega) : a ⊓ (a ⇨ b) ≤ b := by
  exact Reentry.inf_himp_le (R := R) a b

end BoundaryHeyting

end LoF
end HeytingLean
