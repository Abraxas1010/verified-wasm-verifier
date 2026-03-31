import HeytingLean.LoF.Combinators.Category.Completion2PathBicategory

/-!
# Smoke test: non-thin completion 2-path quotient bicategory

This file checks that:
- the quotient hom-categories are available, and
- any completion square yields a 2-morphism in the quotient hom-category.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open CategoryTheory
open HeytingLean.LoF
open HeytingLean.LoF.Comb
open HeytingLean.LoF.Combinators.Category

#check skyCompletion2PathQuotBicategory

example {t : Comb} (c : Completion t) :
    (by
        let a : MWObj := ⟨t⟩
        let b : MWObj := ⟨c.w⟩
        letI : Category (a ⟶ b) := Completion2PathQuot.homCategory a b
        exact (Completion.leftPath c ⟶ Completion.rightPath c)) := by
  let a : MWObj := ⟨t⟩
  let b : MWObj := ⟨c.w⟩
  letI : Category (a ⟶ b) := Completion2PathQuot.homCategory a b
  exact Quot.mk _ (Completion2Path.of_completion c)

end LoF
end Tests
end HeytingLean

