import HeytingLean.Bridge.NoCoincidence.Nucleus.AdviceAsNucleus
import HeytingLean.Bridge.Veselov.HybridZeckendorf.WeightSystem

namespace HeytingLean.Bridge.NoCoincidence.Structure

open HeytingLean.Bridge.NoCoincidence.Basic
open HeytingLean.Bridge.Veselov.HybridZeckendorf

/-- Advice is organized into at most three HZ-style scales. -/
def adviceLevel (C : RevCircuit n) : ℕ :=
  min 2 C.size

/-- Weight attached to the highest active scale in the advice decomposition. -/
def adviceWeight (C : RevCircuit n) : ℕ :=
  weight (adviceLevel C + 1)

theorem adviceLevel_le_two (C : RevCircuit n) : adviceLevel C ≤ 2 := by
  simp [adviceLevel]

theorem adviceWeight_pos (C : RevCircuit n) : 0 < adviceWeight C := by
  unfold adviceWeight
  exact weight_pos _

theorem hierarchical_advice_polynomial (C : RevCircuit n) :
    ∃ k ≤ 2, adviceWeight C = weight (k + 1) := by
  refine ⟨adviceLevel C, adviceLevel_le_two C, rfl⟩

end HeytingLean.Bridge.NoCoincidence.Structure
