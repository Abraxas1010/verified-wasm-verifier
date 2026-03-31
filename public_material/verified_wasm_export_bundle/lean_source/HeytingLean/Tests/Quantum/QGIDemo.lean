import HeytingLean.Quantum.QGIContext
import HeytingLean.Quantum.QGIPhaseLaw
import HeytingLean.Quantum.VacuumOmegaRBridge

/-
End-to-end QGI + Ωᴿ demo scaffold.

This module provides:
* A concrete QGI-flavoured `VacuumOmegaRContext` (`demoContext`).
* A `VacuumGravityBridge` over that context (`demoBridge`).
* A small list of sample (m, g, T) parameter triples.
* A derived list of symbolic phase values pairing `t3Phase` and
  `gaugePhase` for those samples.

It is intended for interactive exploration (e.g. via `#eval` in an
editor) rather than for production use or CLI wiring.
-/

namespace HeytingLean.Tests.Quantum

open HeytingLean.Quantum
open HeytingLean.Quantum.QGIContext
open HeytingLean.Quantum.QGIPhaseLaw
open HeytingLean.Quantum.VacuumOmegaRBridge
open HeytingLean.Quantum.GravitationalCollapse
open HeytingLean.Quantum.VacuumOmegaRBridge.QGI

/-- Sample parameter triples (m, g, T) for the QGI demo. -/
def sampleParams : List (ℝ × ℝ × ℝ) :=
  [ (1.0e-27, 9.8, 0.1),
    (1.0e-27, 9.8, 0.2),
    (1.0e-27, 9.8, 0.3) ]

/-- Demo gravitational/phase parameter record. -/
noncomputable def demoParams : PhysParams :=
  { hbar := 1.0, G := 1.0 }

/-- Concrete Ωᴿ context for the QGI example. -/
noncomputable def demoContext : VacuumOmegaRContext β (Set β) :=
  qgiBaseContext

/-- Default bridge over the QGI context, reusing the abstract constructor. -/
noncomputable def demoBridge : VacuumGravityBridge demoContext :=
  mkDefaultBridge (C := demoContext)

-- Sanity: the core vacuum ↔ Euler-boundary equivalence is available.
#check (demoBridge.vacuum_equals_euler :
  demoContext.vacuumOmega = demoContext.R.eulerBoundary)

/-- Concrete QGI phase model specialised to the `demoContext`. -/
noncomputable def demoQGIPhaseModel :
    VacuumGravityBridge.QGIPhaseModel demoContext :=
  by
    -- `demoContext` is definitionally `qgiBaseContext`.
    simpa [demoContext] using qgiPhaseModel

/-- Bridge over `demoContext` that uses the nontrivial laboratory /
    free-fall frame pair from `demoQGIPhaseModel`. -/
noncomputable def demoQGIBridge :
    VacuumGravityBridge demoContext :=
  by
    simpa [demoContext] using qgiBridge

/-- Symbolic phase samples for the QGI demo: for each (m, g, T) we record
    `t3PhaseR` and the corresponding `gaugePhaseR` as functions of the demo
    parameters and bridge. -/
noncomputable def samplePhaseTable
    (P : PhysParams)
    (B : VacuumGravityBridge demoContext) :
    List (ℝ × ℝ × ℝ × ℝ × ℝ) :=
  sampleParams.map (fun (m, g, T) =>
    let φ_t3 := t3PhaseR P m g T
    let φ_gauge :=
      gaugePhaseR (C := demoContext) P
        B.qgi.frameLab B.qgi.frameFree m g T
    (m, g, T, φ_t3, φ_gauge))

-- A concrete table using `demoParams` and `demoBridge`.
noncomputable def demoPhaseTable :
    List (ℝ × ℝ × ℝ × ℝ × ℝ) :=
  samplePhaseTable demoParams demoBridge

/-!
Two derived tables that make the frame choice explicit:

* `demoPhaseTable_lab_lab` uses the trivial laboratory/laboratory frame
  pair from `demoBridge`.
* `demoPhaseTable_lab_free` uses the laboratory/free-fall frame pair
  from `demoQGIBridge`.
-/

noncomputable def demoPhaseTable_lab_lab :
    List (ℝ × ℝ × ℝ × ℝ × ℝ) :=
  samplePhaseTable demoParams demoBridge

noncomputable def demoPhaseTable_lab_free :
    List (ℝ × ℝ × ℝ × ℝ × ℝ) :=
  samplePhaseTable demoParams demoQGIBridge

-- Sanity: in the QGI-labelled model, the gauge phase is identified
-- with the symbolic T³ profile.
#check
  (VacuumOmegaRBridge.QGIPhaseModel.gaugePhase_properties
    (C := demoContext) demoQGIBridge.qgi)

end HeytingLean.Tests.Quantum
