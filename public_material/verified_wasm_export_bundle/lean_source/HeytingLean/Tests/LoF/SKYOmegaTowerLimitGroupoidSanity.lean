import HeytingLean.LoF.Combinators.Category.OmegaTowerLimitGroupoid

/-!
# Smoke test: formal ω-groupoid tower + truncation bridge (Phase A.4)
-/

namespace HeytingLean
namespace Tests
namespace LoF

open CategoryTheory
open HeytingLean.LoF
open HeytingLean.LoF.Comb
open HeytingLean.LoF.Combinators.Category

open Combinators.Category.FormalOmegaGroupoid
open Combinators.Category.TruncationBridge

noncomputable section

-- The ω-limit of the Arrow tower on the free groupoid is itself a groupoid.
example : Groupoid OmegaLeft := by infer_instance
example : Groupoid OmegaRight := by infer_instance

-- Path truncation bridge: reachability is mere existence of labeled paths.
example (t u : Comb) : Comb.Steps t u ↔ Nonempty (LSteps t u) :=
  steps_iff_nonempty_lsteps t u

-- Closure-kernel quotient equals closed sieves on the reachability site.
example (X : HeytingLean.LoF.Combinators.Topos.StepsCat) :
    HeytingLean.LoF.Combinators.Topos.CloseQuot
        (J := HeytingLean.LoF.Combinators.Topos.stepsDenseTopology) X ≃
      HeytingLean.LoF.Combinators.Topos.ClosedSieve
        HeytingLean.LoF.Combinators.Topos.stepsDenseTopology X :=
  closeQuotEquivClosed_stepsDense X

end

end LoF
end Tests
end HeytingLean
