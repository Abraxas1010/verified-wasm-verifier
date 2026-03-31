import HeytingLean.LoF.Correspondence.LoFSKY

/-!
Sanity checks for `HeytingLean.LoF.Correspondence.LoFSKY`.

This is compile-only + small proof checks that:
- `LoFTerm ≃ Comb` via `LoFTerm.equivSKY`,
- one-step LoF reductions map to SKY reductions under `LoFTerm.toSKY`.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.LoF
open HeytingLean.LoF.Correspondence

#check LoFTerm.toSKY_bijective

open Correspondence.LoFStep

private def t : LoFTerm :=
  LoFTerm.app (LoFTerm.app LoFTerm.unmark LoFTerm.mark) LoFTerm.reentry

-- LoF one-step: (unmark mark reentry) ↦ mark
example : Step t LoFTerm.mark :=
  Step.unmark_rule _ _

-- Under the correspondence, this is just the SKY `K`-rule.
example : Comb.Step (LoFTerm.toSKY t) (LoFTerm.toSKY LoFTerm.mark) :=
  step_toSKY (Step.unmark_rule _ _)

end LoF
end Tests
end HeytingLean
