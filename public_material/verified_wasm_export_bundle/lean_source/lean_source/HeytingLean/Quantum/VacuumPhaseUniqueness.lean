import HeytingLean.Quantum.VacuumOmegaR
import HeytingLean.Quantum.QGIPhaseLaw

/-
# Phase / T³-based uniqueness of the vacuum (symbolic layer)

This module lives strictly in the physics-facing layer. It provides a
small amount of structure around the symbolic T³ phase law
`t3PhaseR` together with an abstract “mass model” and proves that,
under clear modelling assumptions, the Ωᴿ vacuum is uniquely
characterised by having identically zero T³ phase.

Nothing in this file is used by the core LoF or Ωᴿ theory; all
dependencies flow outward into physics-oriented models only.
-/

namespace HeytingLean
namespace Quantum
namespace VacuumPhaseUniqueness

open Quantum
open QGIPhaseLaw

universe u v

variable {β : Type u} {α : Type v}
variable [OML.OrthocomplementedLattice β] [OML.OrthomodularLattice β]
variable [LoF.PrimaryAlgebra α]

/-- Abstract mass model over a given `VacuumOmegaRContext` and physical
parameter set `P`.  It assigns a real-valued “mass” to each Ωᴿ fixed
point and records two modelling assumptions:

* vanishing T³ phase is equivalent to vanishing mass;
* the vacuum is the unique Ωᴿ point of zero mass.

These are *assumptions* about a particular physical model; they are
never used in the core logic / Ωᴿ equivalence proofs. -/
structure PhaseMassModel (C : VacuumOmegaRContext β α)
    (P : GravitationalCollapse.PhysParams) where
  /-- Real-valued “mass” assigned to each Ωᴿ fixed point. -/
  massOf : C.R.Omega → ℝ
  /-- In this model, vanishing T³ phase is equivalent to vanishing mass
      for all non-degenerate gravitational configurations. -/
  t3_zero_iff_mass_zero :
    ∀ (ψ : C.R.Omega) (g T : ℝ), g ≠ 0 → T > 0 →
      (t3PhaseR P (massOf ψ) g T = 0 ↔ massOf ψ = 0)
  /-- The Ωᴿ vacuum is the unique zero-mass fixed point. -/
  unique_zero_mass :
    ∀ ψ : C.R.Omega, massOf ψ = 0 → ψ = C.vacuumOmega

/-- Zero T³ phase uniquely characterises the vacuum among Ωᴿ fixed points,
provided we work in a `PhaseMassModel` that:

* equates vanishing T³ phase with vanishing mass, and
* treats the vacuum as the unique zero-mass state. -/
lemma vacuum_unique_by_zero_phase
    (C : VacuumOmegaRContext β α)
    (P : GravitationalCollapse.PhysParams)
    (M : PhaseMassModel C P)
    (ψ : C.R.Omega)
    (h : ∀ g T, g ≠ 0 → T > 0 →
        t3PhaseR P (M.massOf ψ) g T = 0) :
    ψ = C.vacuumOmega := by
  -- Specialise the assumption to a single non-degenerate configuration,
  -- e.g. `g = 1`, `T = 1`, to recover that `massOf ψ = 0`.
  have h_phase :
      t3PhaseR P (M.massOf ψ) (1 : ℝ) (1 : ℝ) = 0 := by
    have hg : (1 : ℝ) ≠ 0 := by norm_num
    have hT : (1 : ℝ) > 0 := by norm_num
    exact h 1 1 hg hT
  have h_mass_zero :
      M.massOf ψ = 0 := by
    have hiff := M.t3_zero_iff_mass_zero ψ (1 : ℝ) (1 : ℝ) (by norm_num) (by norm_num)
    exact (hiff.mp h_phase)
  -- Apply the uniqueness assumption of the mass model.
  exact M.unique_zero_mass ψ h_mass_zero

end VacuumPhaseUniqueness
end Quantum
end HeytingLean

