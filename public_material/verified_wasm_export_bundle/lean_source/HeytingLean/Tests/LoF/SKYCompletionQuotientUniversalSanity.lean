import HeytingLean.LoF.Combinators.Category.CompletionQuotientUniversal

/-!
# Smoke test: universal property of the completion quotient
-/

namespace HeytingLean
namespace Tests
namespace LoF

open CategoryTheory
open HeytingLean.LoF
open HeytingLean.LoF.Comb
open HeytingLean.LoF.Combinators.Category

#check CompletionHomotopy.Respects
#check CompletionHomotopy.liftFunctor
#check CompletionHomotopy.fac
#check CompletionHomotopy.uniq

end LoF
end Tests
end HeytingLean

