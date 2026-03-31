import HeytingLean.IteratedVirtual.BendingEnergy

/-!
# Tests.IteratedVirtual.BendingEnergySanity

Compile-only checks for the discrete bending energy layer.
-/

namespace HeytingLean
namespace Tests
namespace IteratedVirtual

open HeytingLean.IteratedVirtual

section
  #check bendingEnergy
  #check bendingEnergy_eq_zero_iff_secondDiff_eq_zero
  #check affine_on_prefix_of_secondDiff_eq_zero

  -- Trivial constant sequence has zero bending energy.
  def zeroSeq : Nat → ℝ := fun _ => 0

  example (k : Nat) : secondDiff (p := zeroSeq) k = 0 := by
    simp [secondDiff, zeroSeq]

  example (N : Nat) : bendingEnergy (p := zeroSeq) N = 0 := by
    have hsd : ∀ k : Nat, k < N → secondDiff (p := zeroSeq) k = 0 := by
      intro k hk
      simp [secondDiff, zeroSeq]
    exact (bendingEnergy_eq_zero_iff_secondDiff_eq_zero (p := zeroSeq) (N := N)).2 hsd
end

end IteratedVirtual
end Tests
end HeytingLean
