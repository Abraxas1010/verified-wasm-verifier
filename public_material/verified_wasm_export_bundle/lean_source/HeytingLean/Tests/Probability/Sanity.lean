import HeytingLean.Probability.Discrete
import HeytingLean.Probability.Step
import HeytingLean.Probability.Nucleus

/-! Compile-only sanity for Discrete probability lens. -/

namespace HeytingLean
namespace Tests
namespace Probability

open HeytingLean.Probability
instance : Inhabited String := ⟨""⟩

noncomputable def coins : HeytingLean.Probability.Dist String :=
  let xs : Array (String × ℝ) := #[("H", 1), ("T", 1)]
  Dist.fromPairs xs

noncomputable def biased : HeytingLean.Probability.Dist Nat :=
  let xs : Array (Nat × ℝ) := #[(0, 1), (1, 3)]
  Dist.fromPairs xs

/-- Build and map a small coin distribution to ensure the discrete probability
API is available and well-typed. -/
noncomputable def _coinSupportSize : Nat := by
  let d := coins
  let f : String → Nat := fun s => if s = "H" then 1 else 0
  let d' := Dist.map f d
  exact d'.support.size

end Probability
end Tests
end HeytingLean
