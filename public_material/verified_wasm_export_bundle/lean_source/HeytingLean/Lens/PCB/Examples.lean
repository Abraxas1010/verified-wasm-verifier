import HeytingLean.Lens.PCB.Multi
import HeytingLean.Lens.PCB.Distance
import HeytingLean.Lens.PCB.ReentryInstances
import HeytingLean.LoF.Nucleus
import Mathlib.Data.Real.Basic

/-!
Examples for PCB Multi policy with score‑based lifting.
Provides simple `Score` instances and a helper that builds a policy
using `liftScoreFrom`.
-/

namespace HeytingLean
namespace Lens
namespace PCB

open HeytingLean.Probability

/-- Score by string length (as ℝ). -/
instance : Score String where
  score s := (String.length s : ℝ)

/-- Distance by absolute difference of lengths. -/
instance : Distance String where
  dist a b := |(String.length a : ℝ) - (String.length b : ℝ)|

/-- Trivial score for Reentry fixed points: constant 1 (neutral). -/
def scoreOmega {α} [LoF.PrimaryAlgebra α] (R : LoF.Reentry α) : R.Omega → Real := fun _ => 1

/-- Build a score‑based policy for String using identity lift and length score. -/
noncomputable def stringScorePolicy : MultiUpdatePolicy String :=
  liftScoreFrom (Ω := String) (lift := id) (score := Score.score)

/-- Build a score‑based policy for `R.Omega` using identity lift and constant score. -/
noncomputable def omegaScorePolicy {α} [LoF.PrimaryAlgebra α]
  (R : LoF.Reentry α) : MultiUpdatePolicy (R.Omega) :=
  liftScoreFrom (Ω := R.Omega) (lift := id) (score := scoreOmega R)

end PCB
end Lens
end HeytingLean
