import HeytingLean.LoF.Combinators.Category.PathTruncation
import HeytingLean.LoF.Combinators.SKY

/-!
Compile-only sanity checks for the “path truncation bridge”:

* thin reachability `Comb.Steps` ⇔ `Nonempty (LSteps ...)`
* and `Comb.Steps → Trunc (LSteps ...)` (classical direction)
-/

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.LoF
open HeytingLean.LoF.Comb
open HeytingLean.LoF.Combinators.Category

#check PathTruncation.steps_iff_nonempty_lsteps
#check PathTruncation.steps_of_trunc_lsteps
#check PathTruncation.trunc_lsteps_of_steps

example :
    Comb.Steps (Comb.app (Comb.app .K .S) .Y) .S :=
  Comb.Steps.trans (Comb.Step.K_rule (x := .S) (y := .Y)) (Comb.Steps.refl .S)

example :
    Nonempty (LSteps (Comb.app (Comb.app .K .S) .Y) .S) := by
  -- Use the bridge from propositional reachability.
  refine
    (PathTruncation.steps_iff_nonempty_lsteps (t := (Comb.app (Comb.app .K .S) .Y)) (u := .S)).1 ?_
  exact Comb.Steps.trans (Comb.Step.K_rule (x := .S) (y := .Y)) (Comb.Steps.refl .S)

end LoF
end Tests
end HeytingLean
