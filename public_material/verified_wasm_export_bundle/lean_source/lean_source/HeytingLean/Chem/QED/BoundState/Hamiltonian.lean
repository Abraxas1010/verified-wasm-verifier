import Mathlib.Algebra.Module.LinearMap.Basic
import HeytingLean.Chem.QED.Dirac
import HeytingLean.Chem.QED.BoundState.RadiativePotentials

/-!
# Bound-state effective Hamiltonians (interface layer)

This module defines a small interface for the effective Hamiltonians typically used in
relativistic quantum chemistry / bound-state QED workflows. We stay at the level of
*operators and terms*, without attempting PDE/functional-analysis foundations at M0/M1.

Key idea: make the decomposition explicit:
  H_total = H_base + sum(corrections)

where:
- `H_base` may correspond to a Dirac-Coulomb or Dirac-Coulomb-Breit model, and
- `corrections` are radiative/QED terms (e.g. Uehling vacuum polarization).
-/

namespace HeytingLean
namespace Chem
namespace QED
namespace BoundState

universe u

/-- A Hamiltonian on a state space `S` over scalars `𝕜`, represented as a linear endomorphism. -/
structure Hamiltonian (𝕜 : Type u) [CommRing 𝕜] (S : Type u) [AddCommGroup S] [Module 𝕜 S] where
  H : S →ₗ[𝕜] S

attribute [simp] Hamiltonian.H

/-- A base bound-state model, with a named Hamiltonian and optional decomposition metadata. -/
structure BaseModel (𝕜 : Type u) [CommRing 𝕜] (S : Type u) [AddCommGroup S] [Module 𝕜 S] where
  name : String := "base"
  ham  : Hamiltonian 𝕜 S

/-- An effective Hamiltonian with explicit radiative correction terms. -/
structure EffectiveModel (𝕜 : Type u) [CommRing 𝕜] (S : Type u) [AddCommGroup S] [Module 𝕜 S] where
  base        : BaseModel 𝕜 S
  corrections : List CorrectionTerm := []

/-- Forget the metadata and get the underlying operator for the base model. -/
def BaseModel.op {𝕜 : Type u} [CommRing 𝕜] {S : Type u} [AddCommGroup S] [Module 𝕜 S]
    (M : BaseModel 𝕜 S) : S →ₗ[𝕜] S :=
  M.ham.H

/-- Total operator: for now we treat "corrections" as metadata. Later phases can attach actual operators. -/
def EffectiveModel.op {𝕜 : Type u} [CommRing 𝕜] {S : Type u} [AddCommGroup S] [Module 𝕜 S]
    (M : EffectiveModel 𝕜 S) : S →ₗ[𝕜] S :=
  M.base.op

end BoundState
end QED
end Chem
end HeytingLean
