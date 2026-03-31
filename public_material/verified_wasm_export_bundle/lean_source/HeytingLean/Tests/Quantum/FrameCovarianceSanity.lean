import HeytingLean.Quantum.FrameCovariance
import HeytingLean.Quantum.VacuumOmegaR
import HeytingLean.Quantum.QGIContext

/-
Compile-only sanity checks for the frame covariance layer.
-/

namespace HeytingLean.Tests.Quantum

open HeytingLean.Quantum
open HeytingLean.Quantum.QGIContext
open HeytingLean.Quantum.FrameCovariance
open HeytingLean.Quantum.FrameCovariance.QGI

-- Check the frame transform abstraction.
#check FrameTransform

-- Check the QEP predicate and vacuum lemma.
#check QuantumEquivalencePrinciple
#check vacuum_qep_laboratory

-- Check the concrete QGI free-fall frame.
#check freeFallFrame

-- Sanity: on the QGI finite lattice, the free-fall frame swaps the two arms.
example :
    freeFallFrame.map labPath = freePath ∧
    freeFallFrame.map freePath = labPath := by
  constructor <;> rfl

-- Sanity: the QGI free-fall frame preserves complements and meets on
-- a few concrete elements.
example :
    freeFallFrame.map
        (Quantum.OML.OrthocomplementedLattice.compl labPath)
      = Quantum.OML.OrthocomplementedLattice.compl
          (freeFallFrame.map labPath) := by
  -- This is a direct instance of `freeFallMap_preserves_compl`.
  simpa using freeFallMap_preserves_compl labPath

example :
    freeFallFrame.map (labPath ⊓ freePath)
      = freeFallFrame.map labPath ⊓ freeFallFrame.map freePath := by
  -- And similarly for meets.
  simpa using freeFallMap_preserves_inf labPath freePath

-- Sanity: in the concrete QGI base context, the vacuum satisfies QEP
-- for the nontrivial free-fall frame.
#check vacuum_qep_freeFall_qgi

end HeytingLean.Tests.Quantum
