import HeytingLean.IteratedVirtual.BendingEnergyMinimization

/-!
# Tests.IteratedVirtual.BendingEnergyMinimizationSanity

Compile-only checks for the constrained minimization / uniqueness layer.
-/

namespace HeytingLean
namespace Tests
namespace IteratedVirtual

open HeytingLean.IteratedVirtual

section
  #check affineFrom01
  #check bendingEnergy_affineFrom01_eq_zero
  #check bendingEnergy_minimizer_affineFrom01
  #check bendingEnergy_minimizer_unique

  example : affineFrom01 (V := ℝ) 0 1 3 = 3 := by
    simp [affineFrom01]

  -- Uniqueness statement specialized to a single index, under boundary + zero-energy hypotheses.
  example (N : Nat) (p : Nat → ℝ) (h0 : p 0 = 0) (h1 : p 1 = 1) (hE : bendingEnergy p N = 0)
      (hk : 3 ≤ N + 1) : p 3 = 3 := by
    have := eq_affineFrom01_of_bendingEnergy_eq_zero_and_boundary (V := ℝ) (a := 0) (b := 1) (N := N) (p := p) h0 h1 hE 3 hk
    simpa [affineFrom01] using this
end

end IteratedVirtual
end Tests
end HeytingLean

