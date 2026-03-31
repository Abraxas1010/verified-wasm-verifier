import HeytingLean.Quantum.OML.Examples.O6

open HeytingLean.Quantum.OML O6

example : O6.nondistrib := O6.nondistrib

-- Orthomodular law holds by the instance; we sanity-check a few cases
example : O6.u ≤ O6.top := by simp [O6.le_def]
example : O6.top = O6.u ⊔ (O6.compl O6.u ⊓ O6.top) := by rfl
