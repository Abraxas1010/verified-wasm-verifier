import HeytingLean.Bridge.NoCoincidence.Nucleus.NucleusDecomposition
import HeytingLean.Generative.SpatialClosure
import HeytingLean.Generative.FourDBarrier

namespace HeytingLean.Bridge.NoCoincidence.Structure

open HeytingLean.Bridge.NoCoincidence.Nucleus
open HeytingLean.Generative

/-- The current no-coincidence decomposition is organized around three named advice components. -/
def canonicalLensCount : ℕ := 3

/-- This calibration equality imports the existing `level2.dim = 3` fact from the generative
spatial-closure lane; it is a bookkeeping alignment, not a new dimensional theorem. -/
theorem canonicalLensCount_matches_level2_dimension :
    canonicalLensCount = level2.dim := by
  rfl

/-- Every advice string factors through the same three canonical lenses. The dimensional-emergence
story is used only as a bound: three, and no more forced structural components. -/
theorem advice_component_bound (n : ℕ) (π : String) :
    ∃ l₁ l₂ l₃ : NucleusLens n,
      match nucleusFromAdvice n π with
      | none => True
      | some R =>
          R.adviceTag = l₁.lensName ∨ R.adviceTag = l₂.lensName ∨ R.adviceTag = l₃.lensName := by
  simpa [canonicalLensCount_matches_level2_dimension] using
    recognized_advice_uses_one_of_three_lenses n π

theorem no_fourth_forced_lens :
    emergenceStatus 2 = .barrier := by
  exact level2_barrier

end HeytingLean.Bridge.NoCoincidence.Structure
