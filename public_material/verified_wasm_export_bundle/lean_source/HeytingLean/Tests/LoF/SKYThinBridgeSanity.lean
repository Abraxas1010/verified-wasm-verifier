import HeytingLean.LoF.Combinators.Category.ThinBridge

/-!
Compile-only sanity checks for the thin↔non-thin bridge.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open CategoryTheory
open HeytingLean.LoF
open HeytingLean.LoF.Comb
open HeytingLean.LoF.Combinators.Category

#check forgetToStepsCat

-- The functor lands in the preorder category on `Comb`.
example : MWObj ⥤ HeytingLean.LoF.Comb :=
  forgetToStepsCat

end LoF
end Tests
end HeytingLean

