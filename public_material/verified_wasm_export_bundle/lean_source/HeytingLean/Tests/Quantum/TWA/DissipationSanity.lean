import HeytingLean.Quantum.TWA.Dissipation

namespace HeytingLean
namespace Tests
namespace Quantum
namespace TWA

open HeytingLean.Quantum.TWA
open scoped ComplexConjugate

/-! Compile-time sanity checks for `TWA.Dissipation`. -/

example {N : ℕ} (H loss : SpinConfig N → ℝ) (s : SpinConfig N) :
    conj (effectiveHamiltonian (N := N) H loss s)
      = (H s : ℂ) + Complex.I * (loss s : ℂ) := by
  simp

example : True := by trivial

end TWA
end Quantum
end Tests
end HeytingLean
