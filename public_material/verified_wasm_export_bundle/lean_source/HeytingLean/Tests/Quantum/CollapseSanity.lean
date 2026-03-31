import HeytingLean.Quantum.GravitationalCollapse
import HeytingLean.Quantum.VacuumOmegaR
import HeytingLean.Quantum.QGIContext

/-
Compile-only sanity checks for the symbolic gravitational collapse layer.
-/

namespace HeytingLean.Tests.Quantum

open HeytingLean.Quantum
open HeytingLean.Quantum.GravitationalCollapse
open HeytingLean.Quantum.QGIContext
open HeytingLean.Quantum.OML.QGIInterferometer

-- Check the physical-parameter record and core functions.
#check PhysParams
#check gravitationalSelfEnergy
#check penroseCollapseTime
#check SuperpositionStable
#check VacuumStable

-- Check the vacuum stability lemma.
#check vacuum_no_collapse

-- Check the abstract collapse-to-Euler dynamics scaffold.
#check CollapseToEuler
#check CollapseToEuler.iterate
#check CollapseToEuler.iterate_succ_le_euler

-- Concrete QGI collapse examples.
#check qgiCollapseToEuler
 #check qgiCollapseToEulerSoft

-- Sanity lemma: the first iterate of the QGI collapse sends any ambient
-- configuration to the Euler boundary of `qgiBaseContext`.
example (a : Set β) :
    CollapseToEuler.iterate qgiCollapseToEuler 1 a =
      qgiBaseContext.R.eulerBoundary := by
  simp [CollapseToEuler.iterate, qgiCollapseToEuler]

-- Softer collapse: sets containing `labPath` collapse to the Euler boundary.
example :
    CollapseToEuler.iterate qgiCollapseToEulerSoft 1
      ({b : β | b = labPath} : Set β) =
      qgiBaseContext.R.eulerBoundary := by
  classical
  -- In this case the guard predicate is true.
  have h : (fun s : Set β => labPath ∈ s ∨ freePath ∈ s)
      ({b : β | b = labPath} : Set β) := by
    left; simp
  simp [CollapseToEuler.iterate, qgiCollapseToEulerSoft, collapseIf, h]

-- Softer collapse: sets containing neither arm collapse to bottom.
example :
    CollapseToEuler.iterate qgiCollapseToEulerSoft 1
      (∅ : Set β) =
      (⊥ : Set β) := by
  classical
  -- Here the guard predicate is false.
  have h :
      ¬ (fun s : Set β => labPath ∈ s ∨ freePath ∈ s) (∅ : Set β) := by
    simp
  simp [CollapseToEuler.iterate, qgiCollapseToEulerSoft, collapseIf, h]

end HeytingLean.Tests.Quantum
