import HeytingLean.LoF.Combinators.Category.Completion3Cell

/-!
# Smoke test: explicit 3-cells for completion 2-path coherence

This file checks that:
- the 3-cell layer `Completion3Cell` is available, and
- Prop-level coherence steps (`Completion2PathRel`) can be reified as explicit 3-cell data.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open CategoryTheory
open HeytingLean.LoF
open HeytingLean.LoF.Comb
open HeytingLean.LoF.Combinators.Category

#check Completion3Cell
#check Completion3Cell.nonempty_ofRel

example {a b c : MWObj} (f : a ⟶ b) (g : b ⟶ c) :
    Nonempty
      (Completion3Cell
        (Completion2Path.whiskerLeft f (Completion2Path.id g))
        (Completion2Path.id (f ≫ g))) :=
  Completion3Cell.nonempty_ofRel (Completion2PathRel.whisker_left_id (f := f) (g := g))

example {t : Comb} (c : Completion t) :
    let a : MWObj := ⟨t⟩
    Completion3Cell
      (Completion2Path.whiskerLeft (𝟙 a) (Completion2Path.of_completion c))
      (Completion2Path.vcomp
        (Completion2Path.eqToHom (LSteps.comp_refl_left (Completion.leftPath c)))
        (Completion2Path.vcomp (Completion2Path.of_completion c)
          (Completion2Path.eqToHom (LSteps.comp_refl_left (Completion.rightPath c))))) := by
  intro a
  simpa using (Completion3Cell.id_whisker_left (η := Completion2Path.of_completion c))

end LoF
end Tests
end HeytingLean
