import Mathlib.Data.Real.Basic
import HeytingLean.Quantum.VacuumOmegaR
import HeytingLean.Quantum.FrameCovariance
import HeytingLean.Quantum.GravitationalCollapse

/-!
# QGI‑style T³ phase law (symbolic + Float CLI)

This module introduces two closely related versions of the T³ phase law
that appears in Penrose–Fuentes‑style Quantum Galileo Interferometer
(QGI) scenarios:

* a **real‑valued** symbolic profile `t3PhaseR` used by the abstract
  QGI model and bridge; and
* a **Float‑valued** profile `t3Phase` used by the numeric CLI layer.

The goal is to keep the physics‑facing numerics in `Float` (so they can
be printed and consumed easily by tooling) while preserving a clean
`ℝ`‑valued interface for symbolic reasoning inside the library.
-/

namespace HeytingLean
namespace Quantum
namespace QGIPhaseLaw

open Quantum
open Quantum.FrameCovariance
open Quantum.GravitationalCollapse

universe u v

/-! ## Real-valued symbolic phase law -/

/-- Symbolic T³ phase profile over `ℝ`.

`t3PhaseR P m g T` is intended to represent a phase of the form

  φ(T) = - (m g² T³) / (3 ħ)

up to dimensionful constants and experimental details. Here:

* `P : PhysParams` packages `ħ` and `G` (unused in the formula).
* `m` is a mass parameter.
* `g` is a gravitational field parameter.
* `T` is a time parameter. -/
noncomputable def t3PhaseR (P : PhysParams) (m g T : ℝ) : ℝ :=
  - (m * g * g * T * T * T) / (3 * P.hbar)

/-- A QGI‑style gauge phase between two frames, modelled symbolically by
    the T³ profile over `ℝ`.  For now the frame arguments are unused;
    they are present to make the interface explicit. -/
noncomputable def gaugePhaseR
    {β : Type u} {α : Type v}
    [Quantum.OML.OrthocomplementedLattice β]
    [Quantum.OML.OrthomodularLattice β]
    [LoF.PrimaryAlgebra α]
    (C : VacuumOmegaRContext β α)
    (P : PhysParams)
    (F₁ F₂ : FrameTransform β)
    (m g T : ℝ) : ℝ :=
  let _ := C
  let _ := F₁
  let _ := F₂
  t3PhaseR P m g T

/-- In the concrete QGI base context, the symbolic gauge phase between
    the laboratory frame and the QGI free‑fall frame agrees with the
    T³ profile `t3PhaseR`. This currently follows by definitional
    equality of `gaugePhaseR` but is exposed as a named lemma to make
    the intended “lab vs free‑fall = T³” relationship explicit. -/
lemma gauge_phase_lab_freefall_qgi
    (P : PhysParams) (m g T : ℝ) :
    gaugePhaseR
      (C := QGIContext.qgiBaseContext)
      P FrameCovariance.laboratoryFrame
        FrameCovariance.QGI.freeFallFrame m g T
      = t3PhaseR P m g T := by
  -- By definition, `gaugePhaseR` ignores the frame arguments and
  -- returns `t3PhaseR P m g T`.
  rfl

/-- If the gravitational field parameter is zero, the real‑valued T³
    phase profile vanishes. This is a purely algebraic fact about
    `t3PhaseR`. -/
lemma t3Phase_zero_g (P : PhysParams) (m T : ℝ) :
    t3PhaseR P m 0 T = 0 := by
  unfold t3PhaseR
  simp

/-- If the gravitational field parameter is zero, the symbolic gauge
    phase over `ℝ` vanishes as well. -/
lemma gaugePhase_zero_g
    {β : Type u} {α : Type v}
    [Quantum.OML.OrthocomplementedLattice β]
    [Quantum.OML.OrthomodularLattice β]
    [LoF.PrimaryAlgebra α]
    (C : VacuumOmegaRContext β α)
    (P : PhysParams)
    (_F₁ _F₂ : FrameTransform β)
    (m T : ℝ) :
    gaugePhaseR (C := C) P _F₁ _F₂ m 0 T = 0 := by
  unfold gaugePhaseR
  simp [t3Phase_zero_g]

/-! ## Float-valued phase law for CLI use -/

/-- Float‑valued analogue of `PhysParams` for numeric QGI demos. -/
structure PhysParamsF where
  hbar : Float
  G    : Float

/-- Float‑valued symbolic T³ phase profile, suitable for CLI use. -/
def t3Phase (P : PhysParamsF) (m g T : Float) : Float :=
  - (m * g * g * T * T * T) / (3.0 * P.hbar)

/-- Float‑valued gauge phase for QGI demos; frame arguments are omitted
    since the current numeric model does not distinguish them. -/
def gaugePhase (P : PhysParamsF) (m g T : Float) : Float :=
  t3Phase P m g T

end QGIPhaseLaw
end Quantum
end HeytingLean
