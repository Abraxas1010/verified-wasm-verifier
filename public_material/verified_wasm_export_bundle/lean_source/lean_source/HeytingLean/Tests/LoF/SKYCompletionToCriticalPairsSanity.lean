import HeytingLean.LoF.Combinators.Category.CompletionToCriticalPairs

/-!
# Smoke test: completion → `StepAt` peak bridge

This file checks that any multiway completion cell determines an underlying positioned one-step peak
in the `StepAt` rewriting layer.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.LoF
open HeytingLean.LoF.Comb
open HeytingLean.LoF.Combinators.Category

#check LStep.toStepAt
#check Completion.toPeak

example {t : Comb} (c : Completion t) : Comb.StepAt.Peak t :=
  Completion.toPeak c

end LoF
end Tests
end HeytingLean

