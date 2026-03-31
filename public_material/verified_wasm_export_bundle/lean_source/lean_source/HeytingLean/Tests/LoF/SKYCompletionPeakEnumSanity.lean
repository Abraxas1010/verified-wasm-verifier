import Mathlib.Tactic
import HeytingLean.LoF.Combinators.Category.CompletionPeakEnum

/-!
Compile + eval sanity checks for `CompletionPeakEnum` (Phase A.2).

We check that:
- enumerated one-step peaks produce at least one bounded completion cell (join bound `≤ 2`).
- the concrete list is evaluable (`#eval`) to support CLI/demo integration.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.LoF
open HeytingLean.LoF.Comb
open HeytingLean.LoF.Combinators.Category

open CompletionPeakEnum

private def left : Comb := Comb.app (Comb.app .K .S) .K
private def right : Comb := Comb.app (Comb.app .K .Y) .K
private def t : Comb := Comb.app left right

-- Inspect the computed generator set (exact order depends on enumeration order).
#eval (completionsFromPeaksUpTo2 t).map (fun c => c.summary)

-- Hard assertion: at least one peak completion is found for this `t` within the uniform bound.
example : (completionsFromPeaksUpTo2 t).isEmpty = false := by
  native_decide

-- Inspect the first completion’s join lengths (if any).
#eval (completionsFromPeaksUpTo2 t).head?.map (fun c => (c.joinLeft.length, c.joinRight.length))

end LoF
end Tests
end HeytingLean

