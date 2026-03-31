import HeytingLean.LoF.Combinators.InfinityGroupoid.SSet

/-!
# Smoke test: SKY ∞-groupoid packaging as a simplicial set

This file checks that the “formal invertibility” layer:

* exists as a simplicial set `SKYInfty : SSet`,
* exposes its truncation tower `SKYInftyTrunc`,
* is a quasicategory as a consequence of being a nerve,
* and now carries the stronger `KanComplex` structure because the repo exports the generic
  theorem that the nerve of a groupoid is Kan.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open CategoryTheory
open SSet
open HeytingLean.LoF.Combinators.InfinityGroupoid

#check SKYInfty
#check SKYInftyTrunc

example : SSet.Quasicategory SKYInfty := by
  infer_instance

example : SSet.KanComplex SKYInfty := by
  infer_instance

end LoF
end Tests
end HeytingLean
