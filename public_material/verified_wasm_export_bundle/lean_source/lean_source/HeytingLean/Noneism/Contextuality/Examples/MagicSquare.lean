import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import HeytingLean.Noneism.Contextuality.GlobalSection
import HeytingLean.LoF.CryptoSheaf.Quantum.MerminPeres

namespace HeytingLean
namespace Noneism
namespace Contextuality
namespace Examples
namespace MagicSquare

open scoped BigOperators
open HeytingLean.LoF.CryptoSheaf.Quantum
open HeytingLean.LoF.CryptoSheaf.Quantum.MerminPeres

abbrev Cell := MPCell
abbrev Outcome := MPVal
abbrev Ctx := Context Cell

private def negOne : Outcome :=
  ⟨(-1 : ℤ), (-1 : ℤ), by simp, by simp⟩

/-- Row contexts in the 3×3 magic square. -/
def rowContext (i : Fin 3) : Ctx :=
  (Finset.univ : Finset Cell).filter (fun p => p.1 = i)

/-- Column contexts in the 3×3 magic square. -/
def colContext (j : Fin 3) : Ctx :=
  (Finset.univ : Finset Cell).filter (fun p => p.2 = j)

abbrev ContextTag := Sum (Fin 3) (Fin 3)

def taggedContext : ContextTag → Ctx
  | .inl i => rowContext i
  | .inr j => colContext j

def cover : Finset Ctx :=
  (Finset.univ : Finset ContextTag).image taggedContext

lemma rowContext_mem_cover (i : Fin 3) : rowContext i ∈ cover := by
  refine Finset.mem_image.mpr ?_
  exact ⟨Sum.inl i, by simp, rfl⟩

lemma colContext_mem_cover (j : Fin 3) : colContext j ∈ cover := by
  refine Finset.mem_image.mpr ?_
  exact ⟨Sum.inr j, by simp, rfl⟩

lemma mem_rowContext (i j : Fin 3) : (i, j) ∈ rowContext i := by
  simp [rowContext]

lemma mem_colContext (i j : Fin 3) : (i, j) ∈ colContext j := by
  simp [colContext]

lemma rowContext_injective : Function.Injective rowContext := by
  intro i k h
  by_cases hik : i = k
  · exact hik
  · exfalso
    apply hik
    have hmem : (i, (0 : Fin 3)) ∈ rowContext i := by simp [rowContext]
    have hmem' : (i, (0 : Fin 3)) ∈ rowContext k := by simpa [h] using hmem
    simpa [rowContext] using hmem'

lemma colContext_injective : Function.Injective colContext := by
  intro i k h
  by_cases hik : i = k
  · exact hik
  · exfalso
    apply hik
    have hmem : ((0 : Fin 3), i) ∈ colContext i := by simp [colContext]
    have hmem' : ((0 : Fin 3), i) ∈ colContext k := by simpa [h] using hmem
    simpa [colContext] using hmem'

lemma rowContext_ne_colContext (i j : Fin 3) : rowContext i ≠ colContext j := by
  fin_cases i <;> fin_cases j <;> decide

def allowed (C : Ctx) (s : LocalAssign C Outcome) : Prop :=
  (∃ i : Fin 3,
    C = rowContext i ∧
    ∃ g : Cell → Outcome,
      (∀ x : {m // m ∈ C}, s x = g x.1) ∧ rowProd g i = 1) ∨
  (∃ j : Fin 3,
    C = colContext j ∧
    ∃ g : Cell → Outcome,
      (∀ x : {m // m ∈ C}, s x = g x.1) ∧
      colProd g j = (if j = (2 : Fin 3) then negOne else 1))

def magicSquareScenario : Scenario Cell Outcome where
  cover := cover
  covers_all := by
    intro m
    exact ⟨rowContext m.1, rowContext_mem_cover m.1, by simp [rowContext]⟩
  Allowed := allowed

lemma rowProd_eq_of_row_sync {i : Fin 3} {g₁ g₂ : Cell → Outcome}
    (hsync : ∀ j : Fin 3, g₁ (i, j) = g₂ (i, j)) :
    rowProd g₁ i = rowProd g₂ i := by
  unfold rowProd
  refine Finset.prod_congr rfl ?_
  intro j _
  exact hsync j

lemma colProd_eq_of_col_sync {j : Fin 3} {g₁ g₂ : Cell → Outcome}
    (hsync : ∀ i : Fin 3, g₁ (i, j) = g₂ (i, j)) :
    colProd g₁ j = colProd g₂ j := by
  unfold colProd
  refine Finset.prod_congr rfl ?_
  intro i _
  exact hsync i

lemma global_implies_row_constraints {g : Cell → Outcome}
    (hGlobal : IsGlobalSection magicSquareScenario g) :
    ∀ i : Fin 3, rowProd g i = 1 := by
  intro i
  have hAllowed := hGlobal (rowContext i) (rowContext_mem_cover i)
  rcases hAllowed with hRow | hCol
  · rcases hRow with ⟨i', hCeq, g', hsync, hprod⟩
    have hi : i = i' := rowContext_injective hCeq
    have hsync' : ∀ j : Fin 3, g (i, j) = g' (i, j) := by
      intro j
      have hx := hsync ⟨(i, j), mem_rowContext i j⟩
      simpa [restrict] using hx
    have hprod' : rowProd g' i = 1 := by simpa [hi] using hprod
    calc
      rowProd g i = rowProd g' i := rowProd_eq_of_row_sync hsync'
      _ = 1 := hprod'
  · rcases hCol with ⟨j, hCeq, _, _, _⟩
    exact False.elim ((rowContext_ne_colContext i j) hCeq)

lemma global_implies_col_constraints {g : Cell → Outcome}
    (hGlobal : IsGlobalSection magicSquareScenario g) :
    ∀ j : Fin 3, colProd g j = (if j = (2 : Fin 3) then negOne else 1) := by
  intro j
  have hAllowed := hGlobal (colContext j) (colContext_mem_cover j)
  rcases hAllowed with hRow | hCol
  · rcases hRow with ⟨i, hCeq, _, _, _⟩
    exact False.elim ((rowContext_ne_colContext i j) hCeq.symm)
  · rcases hCol with ⟨j', hCeq, g', hsync, hprod⟩
    have hj : j = j' := colContext_injective hCeq
    have hsync' : ∀ i : Fin 3, g (i, j) = g' (i, j) := by
      intro i
      have hx := hsync ⟨(i, j), mem_colContext i j⟩
      simpa [restrict] using hx
    have hprod' : colProd g' j = (if j = (2 : Fin 3) then negOne else 1) := by
      simpa [hj] using hprod
    calc
      colProd g j = colProd g' j := colProd_eq_of_col_sync hsync'
      _ = (if j = (2 : Fin 3) then negOne else 1) := hprod'

/-- Pure combinatorial parity obstruction for the magic square with explicit `-1`. -/
theorem no_assignment_explicit :
    ¬ ∃ v : Cell → Outcome,
        (∀ i : Fin 3, rowProd v i = 1) ∧
        (∀ j : Fin 3, colProd v j = (if j = (2 : Fin 3) then negOne else 1)) := by
  classical
  intro h
  rcases h with ⟨v, hrow, hcol⟩

  have hrowAll : (∏ i : Fin 3, rowProd v i) = 1 := by
    simp [hrow]

  have hcolAll : (∏ j : Fin 3, colProd v j) = negOne := by
    calc
      (∏ j : Fin 3, colProd v j) = ∏ j : Fin 3, (if j = (2 : Fin 3) then negOne else 1) := by
        simp [hcol]
      _ = negOne := by
        simp

  have hswap : (∏ i : Fin 3, rowProd v i) = (∏ j : Fin 3, colProd v j) := by
    have h1 : (∏ i : Fin 3, rowProd v i) = ∏ p : Cell, v p := by
      simpa [rowProd] using (Fintype.prod_prod_type (f := fun p : Cell => v p)).symm
    have h2 : (∏ j : Fin 3, colProd v j) = ∏ p : Cell, v p := by
      simpa [colProd] using (Fintype.prod_prod_type_right (f := fun p : Cell => v p)).symm
    exact h1.trans h2.symm

  have : (1 : Outcome) = negOne := by
    calc
      (1 : Outcome) = (∏ i : Fin 3, rowProd v i) := by
        simpa using hrowAll.symm
      _ = (∏ j : Fin 3, colProd v j) := hswap
      _ = negOne := hcolAll

  exact (by
    have hne : (1 : Outcome) ≠ negOne := by decide
    exact hne this)

theorem magicSquare_no_global_section :
    ¬ ∃ g : Cell → Outcome, IsGlobalSection magicSquareScenario g := by
  intro h
  rcases h with ⟨g, hGlobal⟩
  exact no_assignment_explicit ⟨g, global_implies_row_constraints hGlobal, global_implies_col_constraints hGlobal⟩

theorem magicSquare_contextual : Contextual magicSquareScenario :=
  magicSquare_no_global_section

end MagicSquare
end Examples
end Contextuality
end Noneism
end HeytingLean
