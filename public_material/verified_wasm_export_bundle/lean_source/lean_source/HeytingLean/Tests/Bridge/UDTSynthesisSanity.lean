import HeytingLean.Bridge.AlMayahi.UDTSynthesis

/-!
# UDT Synthesis Bridge — Sanity Tests

Lightweight examples exercising the key definitions and theorems
from all five UDT synthesis modules.
-/

namespace HeytingLean.Tests.Bridge.UDTSynthesisSanity

open HeytingLean.Bridge.AlMayahi.UDTSynthesis
open HeytingLean.Eigen

-- ClockRateField sanity
example : clockProjection flatClockRateField 0 = 0 :=
  clockProjection_zero flatClockRateField

example : clockProjection flatClockRateField 42 = 42 :=
  clockProjection_flat 42

example : clockRateDeviation flatClockRateField 0 = 0 :=
  clockRateDeviation_zero flatClockRateField

-- MassGenerationGap sanity
example : nucleusGap 3 (fun _ => (1 : ℝ)) = 0 :=
  nucleusGap_zero_of_nonneg _ (fun _ => by norm_num)

example : 0 ≤ nucleusGap 5 (fun _ => (-1 : ℝ)) :=
  nucleusGap_nonneg 5 _

-- LagrangianReduction sanity
example : ∀ (L : TauFieldPotential), lagrangianDensity L 0 L.τ₀ = -L.V L.τ₀ :=
  fun L => lagrangianDensity_static L L.τ₀

-- FalsifiabilityPredicates sanity
example : MechanismLevel.ontological ≠ MechanismLevel.temporal := by decide

example : allDiscriminators.length = 5 := rfl

-- GapDecompositionBridge sanity
example : totalGap ⟨1, 2, 3, by norm_num, by norm_num, by norm_num⟩ = 6 := by
  simp [totalGap]; norm_num

example : 0 ≤ totalGap ⟨0, 0, 0, le_refl 0, le_refl 0, le_refl 0⟩ :=
  totalGap_nonneg ⟨0, 0, 0, le_refl 0, le_refl 0, le_refl 0⟩

-- SparseProjectionField sanity
example : ∀ (pts : Fin 5 → ℝ) (i : Fin 5),
    deviationVector ⟨flatClockRateField, pts⟩ i = 0 :=
  fun pts i => flat_deviation_zero pts i

example : 0 ≤ deviationTrappedEnergy
    (⟨flatClockRateField, fun (_ : Fin 3) => (0 : ℝ)⟩ : GridSample 3) :=
  deviationTrappedEnergy_nonneg _

example : (flatSparseField 10 (fun _ => 0) 1 one_pos).k = 0 := rfl

-- HZComputationalBridge sanity
example : ArithmeticMode.hz ≠ ArithmeticMode.standard := by decide

end HeytingLean.Tests.Bridge.UDTSynthesisSanity
