import HeytingLean.LoF.Combinators.Category.NFoldCategory

/-!
# Smoke test: completion-homotopy square cells

This file checks that the “weak square” double-category data (`skyCompletionDoubleData`) exists,
and that the trivial identity square is a cell (by reflexivity of `CompletionHomotopy`).
-/

namespace HeytingLean
namespace Tests
namespace LoF

open CategoryTheory
open HeytingLean.LoF
open HeytingLean.LoF.Comb
open HeytingLean.LoF.Combinators.Category

-- The completion-homotopy square data record exists.
#check skyCompletionDoubleData

-- The Type-valued completion square data record also exists.
#check skyCompletionDoubleDataT

example (t : Comb) :
    completionSqCell
      (a := (⟨t⟩ : MWObj)) (b := (⟨t⟩ : MWObj)) (c := (⟨t⟩ : MWObj)) (d := (⟨t⟩ : MWObj))
      (top := 𝟙 (⟨t⟩ : MWObj)) (bottom := 𝟙 (⟨t⟩ : MWObj))
      (left := 𝟙 (⟨t⟩ : MWObj)) (right := 𝟙 (⟨t⟩ : MWObj)) := by
  -- The identity square commutes up to reflexivity.
  simpa [completionSqCell] using (CompletionHomotopy.refl (LSteps.refl t))

example (t : Comb) :
    completionSqCellT
      (a := (⟨t⟩ : MWObj)) (b := (⟨t⟩ : MWObj)) (c := (⟨t⟩ : MWObj)) (d := (⟨t⟩ : MWObj))
      (top := 𝟙 (⟨t⟩ : MWObj)) (bottom := 𝟙 (⟨t⟩ : MWObj))
      (left := 𝟙 (⟨t⟩ : MWObj)) (right := 𝟙 (⟨t⟩ : MWObj)) := by
  -- The identity square has an explicit completion 2-cell witness.
  simpa [completionSqCellT] using (Completion2Cell.refl (LSteps.refl t))

end LoF
end Tests
end HeytingLean
