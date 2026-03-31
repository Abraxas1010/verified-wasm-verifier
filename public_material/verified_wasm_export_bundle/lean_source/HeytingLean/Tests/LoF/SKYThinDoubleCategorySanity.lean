import HeytingLean.LoF.Combinators.Category.DoubleCategory

/-!
# Smoke test: thin double categories for SKY squares

This file checks that:
- the generic commutative-square double category exists, and
- the completion-homotopy square double category on `MWObj` exists and supports horizontal pasting.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open CategoryTheory
open HeytingLean.LoF
open HeytingLean.LoF.Comb
open HeytingLean.LoF.Combinators.Category

#check commSqThinDoubleCategory
#check skyCompletionThinDoubleCategory
#check ThinDoubleCategory.hcomp_assoc
#check ThinDoubleCategory.vcomp_assoc
#check ThinDoubleCategory.interchange

example (t : Comb) :
    let D := skyCompletionThinDoubleCategory
    D.Cell (𝟙 (⟨t⟩ : MWObj)) (𝟙 (⟨t⟩ : MWObj)) (𝟙 (⟨t⟩ : MWObj)) (𝟙 (⟨t⟩ : MWObj)) := by
  intro D
  simpa [skyCompletionThinDoubleCategory, completionSqCell] using
    (D.idCellV (g := 𝟙 (⟨t⟩ : MWObj)))

example (t : Comb) :
    let D := skyCompletionThinDoubleCategory
    D.Cell (𝟙 (⟨t⟩ : MWObj)) (𝟙 (⟨t⟩ : MWObj)) (𝟙 (⟨t⟩ : MWObj)) (𝟙 (⟨t⟩ : MWObj)) := by
  intro D
  have sq :
      D.Cell (𝟙 (⟨t⟩ : MWObj)) (𝟙 (⟨t⟩ : MWObj)) (𝟙 (⟨t⟩ : MWObj)) (𝟙 (⟨t⟩ : MWObj)) := by
    simpa [skyCompletionThinDoubleCategory, completionSqCell] using
      (D.idCellV (g := 𝟙 (⟨t⟩ : MWObj)))
  -- Horizontal pasting of two identity squares is again a cell.
  simpa [skyCompletionThinDoubleCategory] using
    (D.hcomp
      (top₁ := 𝟙 (⟨t⟩ : MWObj)) (top₂ := 𝟙 (⟨t⟩ : MWObj))
      (bottom₁ := 𝟙 (⟨t⟩ : MWObj)) (bottom₂ := 𝟙 (⟨t⟩ : MWObj))
      (left := 𝟙 (⟨t⟩ : MWObj)) (mid := 𝟙 (⟨t⟩ : MWObj)) (right := 𝟙 (⟨t⟩ : MWObj))
      sq sq)

example (t : Comb) :
    let D := skyCompletionThinDoubleCategory
    D.vcomp
        (D.hcomp
          (D.idCellV (g := 𝟙 (⟨t⟩ : MWObj)))
          (D.idCellV (g := 𝟙 (⟨t⟩ : MWObj))))
        (D.hcomp
          (D.idCellV (g := 𝟙 (⟨t⟩ : MWObj)))
          (D.idCellV (g := 𝟙 (⟨t⟩ : MWObj)))) =
      D.hcomp
        (D.vcomp
          (D.idCellV (g := 𝟙 (⟨t⟩ : MWObj)))
          (D.idCellV (g := 𝟙 (⟨t⟩ : MWObj))))
        (D.vcomp
          (D.idCellV (g := 𝟙 (⟨t⟩ : MWObj)))
          (D.idCellV (g := 𝟙 (⟨t⟩ : MWObj)))) := by
  intro D
  exact
    (ThinDoubleCategory.interchange (D := D)
      (sq₁₁ := D.idCellV (g := 𝟙 (⟨t⟩ : MWObj)))
      (sq₁₂ := D.idCellV (g := 𝟙 (⟨t⟩ : MWObj)))
      (sq₂₁ := D.idCellV (g := 𝟙 (⟨t⟩ : MWObj)))
      (sq₂₂ := D.idCellV (g := 𝟙 (⟨t⟩ : MWObj))))

end LoF
end Tests
end HeytingLean
