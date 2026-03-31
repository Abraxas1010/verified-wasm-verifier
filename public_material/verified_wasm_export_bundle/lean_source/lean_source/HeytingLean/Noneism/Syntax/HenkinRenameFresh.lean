import HeytingLean.Noneism.Syntax.Henkin

namespace HeytingLean
namespace Noneism
namespace Syntax
namespace Henkin

/-!
Freshness facts for `renameFormula`.

Track A needs robust control of which variables can appear after alpha-style renaming.
These lemmas are intentionally small and composable.
-/

variable {σ : Type} {κ : Type u}

theorem fvTerm_renameTerm_subset_insert (x y : Var) (t : TermH κ) :
    fvTerm (κ := κ) (renameTerm (κ := κ) x y t) ⊆
      insert y (fvTerm (κ := κ) t) := by
  intro v hv
  cases t with
  | var z =>
      by_cases hz : z = x
      · subst hz
        simp [renameTerm, fvTerm] at hv ⊢
        exact Or.inl hv
      ·
        simp [renameTerm, fvTerm, hz] at hv ⊢
        exact Or.inr hv
  | param k =>
      simp [renameTerm, fvTerm] at hv

theorem fvTerms_renameTerms_subset_insert (x y : Var) (ts : List (TermH κ)) :
    fvTerms (κ := κ) (renameTerms (κ := κ) x y ts) ⊆
      insert y (fvTerms (κ := κ) ts) := by
  induction ts with
  | nil =>
      intro v hv
      simp [renameTerms, fvTerms] at hv
  | cons t ts ih =>
      intro v hv
      simp [renameTerms, fvTerms_cons, Finset.mem_union] at hv ⊢
      rcases hv with hv | hv
      ·
        have hv' : v ∈ insert y (fvTerm (κ := κ) t) :=
          fvTerm_renameTerm_subset_insert (κ := κ) x y t hv
        rcases Finset.mem_insert.1 hv' with hEq | hMem
        · exact Or.inl hEq
        · exact Or.inr (Or.inl hMem)
      ·
        have hv' : v ∈ insert y (fvTerms (κ := κ) ts) := ih hv
        rcases Finset.mem_insert.1 hv' with hEq | hMem
        · exact Or.inl hEq
        · exact Or.inr (Or.inr hMem)

theorem varsFormula_renameFormula_subset_insert (x y : Var) (φ : FormulaH σ κ) :
    varsFormula (σ := σ) (κ := κ) (renameFormula (σ := σ) (κ := κ) x y φ) ⊆
      insert y (varsFormula (σ := σ) (κ := κ) φ) := by
  induction φ with
  | top =>
      intro v hv
      simp [renameFormula, varsFormula] at hv
  | bot =>
      intro v hv
      simp [renameFormula, varsFormula] at hv
  | pred p args =>
      intro v hv
      have :
          v ∈ insert y (fvTerms (κ := κ) args) :=
        fvTerms_renameTerms_subset_insert (κ := κ) x y args (by
          simpa [renameFormula, varsFormula] using hv)
      simpa [varsFormula] using this
  | eExists t =>
      intro v hv
      have :
          v ∈ insert y (fvTerm (κ := κ) t) :=
        fvTerm_renameTerm_subset_insert (κ := κ) x y t (by
          simpa [renameFormula, varsFormula] using hv)
      simpa [varsFormula] using this
  | not φ ih =>
      intro v hv
      have hv' : v ∈ insert y (varsFormula (σ := σ) (κ := κ) φ) := ih (by
        simpa [renameFormula, varsFormula] using hv)
      simpa [renameFormula, varsFormula] using hv'
  | and φ ψ ihφ ihψ =>
      intro v hv
      simp [renameFormula, varsFormula, Finset.mem_union] at hv ⊢
      rcases hv with hv | hv
      ·
        rcases Finset.mem_insert.1 (ihφ hv) with hEq | hMem
        · exact Or.inl hEq
        · exact Or.inr (Or.inl hMem)
      ·
        rcases Finset.mem_insert.1 (ihψ hv) with hEq | hMem
        · exact Or.inl hEq
        · exact Or.inr (Or.inr hMem)
  | or φ ψ ihφ ihψ =>
      intro v hv
      simp [renameFormula, varsFormula, Finset.mem_union] at hv ⊢
      rcases hv with hv | hv
      ·
        rcases Finset.mem_insert.1 (ihφ hv) with hEq | hMem
        · exact Or.inl hEq
        · exact Or.inr (Or.inl hMem)
      ·
        rcases Finset.mem_insert.1 (ihψ hv) with hEq | hMem
        · exact Or.inl hEq
        · exact Or.inr (Or.inr hMem)
  | imp φ ψ ihφ ihψ =>
      intro v hv
      simp [renameFormula, varsFormula, Finset.mem_union] at hv ⊢
      rcases hv with hv | hv
      ·
        rcases Finset.mem_insert.1 (ihφ hv) with hEq | hMem
        · exact Or.inl hEq
        · exact Or.inr (Or.inl hMem)
      ·
        rcases Finset.mem_insert.1 (ihψ hv) with hEq | hMem
        · exact Or.inl hEq
        · exact Or.inr (Or.inr hMem)
  | sigma z φ ih =>
      intro v hv
      by_cases hz : z = x
      · subst hz
        simp [renameFormula, varsFormula, Finset.mem_insert] at hv ⊢
        rcases hv with hEq | hv
        · exact Or.inl hEq
        ·
          rcases Finset.mem_insert.1 (ih hv) with hEq | hMem
          · exact Or.inl hEq
          · exact Or.inr (Or.inr hMem)
      ·
        simp [renameFormula, varsFormula, hz, Finset.mem_insert] at hv ⊢
        rcases hv with hEq | hv
        · exact Or.inr (Or.inl hEq)
        ·
          rcases Finset.mem_insert.1 (ih hv) with hEq | hMem
          · exact Or.inl hEq
          · exact Or.inr (Or.inr hMem)
  | pi z φ ih =>
      intro v hv
      by_cases hz : z = x
      · subst hz
        simp [renameFormula, varsFormula, Finset.mem_insert] at hv ⊢
        rcases hv with hEq | hv
        · exact Or.inl hEq
        ·
          rcases Finset.mem_insert.1 (ih hv) with hEq | hMem
          · exact Or.inl hEq
          · exact Or.inr (Or.inr hMem)
      ·
        simp [renameFormula, varsFormula, hz, Finset.mem_insert] at hv ⊢
        rcases hv with hEq | hv
        · exact Or.inr (Or.inl hEq)
        ·
          rcases Finset.mem_insert.1 (ih hv) with hEq | hMem
          · exact Or.inl hEq
          · exact Or.inr (Or.inr hMem)

theorem not_mem_varsFormula_renameFormula_of_ne
    {a x y : Var} {φ : FormulaH σ κ}
    (hay : a ≠ y)
    (ha : a ∉ varsFormula (σ := σ) (κ := κ) φ) :
    a ∉ varsFormula (σ := σ) (κ := κ) (renameFormula (σ := σ) (κ := κ) x y φ) := by
  intro h
  have h' :
      a ∈ insert y (varsFormula (σ := σ) (κ := κ) φ) :=
    varsFormula_renameFormula_subset_insert (σ := σ) (κ := κ) x y φ h
  rcases Finset.mem_insert.1 h' with hEq | hMem
  · exact hay hEq
  · exact ha hMem

theorem not_mem_varsFormula_renameFormula_of_not_mem_and_ne
    {a x y : Var} {φ : FormulaH σ κ}
    (ha : a ∉ varsFormula (σ := σ) (κ := κ) φ)
    (hay : a ≠ y) :
    a ∉ varsFormula (σ := σ) (κ := κ) (renameFormula (σ := σ) (κ := κ) x y φ) :=
  not_mem_varsFormula_renameFormula_of_ne (σ := σ) (κ := κ) (a := a) (x := x) (y := y)
    hay ha

theorem not_mem_varsFormula_renameFormula_freshVar
    {a x z : Var} {φ : FormulaH σ κ}
    (ha : a ∉ varsFormula (σ := σ) (κ := κ) φ) :
    a ∉ varsFormula (σ := σ) (κ := κ)
      (renameFormula (σ := σ) (κ := κ) z
        (freshVar (varsFormula (σ := σ) (κ := κ) φ ∪ ({x, z, a} : Finset Var))) φ) := by
  let avoid : Finset Var := varsFormula (σ := σ) (κ := κ) φ ∪ ({x, z, a} : Finset Var)
  let z' : Var := freshVar avoid
  have hz'Not : z' ∉ avoid := freshVar_not_mem avoid
  have haInAvoid : a ∈ avoid := by
    refine Finset.mem_union.2 (Or.inr ?_)
    simp
  have haneq : a ≠ z' := by
    intro hEq
    have hz'In : z' ∈ avoid := by
      simpa [hEq] using haInAvoid
    exact hz'Not hz'In
  exact not_mem_varsFormula_renameFormula_of_ne
    (σ := σ) (κ := κ) (a := a) (x := z) (y := z') haneq ha

end Henkin
end Syntax
end Noneism
end HeytingLean
