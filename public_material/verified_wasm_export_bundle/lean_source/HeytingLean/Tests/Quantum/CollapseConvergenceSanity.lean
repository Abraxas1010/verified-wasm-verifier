import HeytingLean.Quantum.GravitationalCollapse
import HeytingLean.Quantum.VacuumOmegaR
import HeytingLean.Quantum.QGIContext

/-
Compile-only sanity checks for the structured collapse-flow abstraction.
-/

namespace HeytingLean.Tests.Quantum

open HeytingLean.Quantum
open HeytingLean.Quantum.GravitationalCollapse
open HeytingLean.Quantum.QGIContext
open HeytingLean.Quantum.OML.QGIInterferometer

variable {β : Type u} {α : Type v}
variable [Quantum.OML.OrthocomplementedLattice β]
variable [Quantum.OML.OrthomodularLattice β]
variable [HeytingLean.LoF.PrimaryAlgebra α]

variable (C : VacuumOmegaRContext β α)

-- Basic API checks.
#check CollapseFlow
#check CollapseFlow.step
#check CollapseFlow.iterate
#check CollapseFlow.iterate_add
#check CollapseFlow.iterate_monotone
#check CollapseFlow.iterate_le_nucleus
#check CollapseFlow.iterate_euler_fixed

-- QGI-specific flow and convergence helpers.
#check QGI.qgiFlowStep
#check QGI.qgiCollapseFlow
#check QGI.collapse_reaches_vacuumOmega_qgi
#check QGI.orbitInf_eq_vacuumOmega_qgi

-- Sanity: the first iterate of the QGI collapse flow simply applies
-- `qgiFlowStep` once.
example (S : Set β) :
    CollapseFlow.iterate QGI.qgiCollapseFlow 1 S =
      QGI.qgiFlowStep S := by
  simp [CollapseFlow.iterate, QGI.qgiCollapseFlow, QGI.qgiFlowStep]

end HeytingLean.Tests.Quantum
