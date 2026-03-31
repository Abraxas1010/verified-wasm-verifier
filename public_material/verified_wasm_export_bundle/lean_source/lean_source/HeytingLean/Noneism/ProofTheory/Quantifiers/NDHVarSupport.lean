import HeytingLean.Noneism.ProofTheory.NDH
import HeytingLean.Noneism.Syntax.HenkinParamToVar

namespace HeytingLean
namespace Noneism
namespace NDH

open Syntax.Henkin

variable {σ κ : Type}

/-- Rewrite a distinguished parameter `k` to variable `a` across a context. -/
def replaceParamWithVarContext [DecidableEq κ]
    (k : κ) (a : Var) (Γ : List (FormulaH σ κ)) : List (FormulaH σ κ) :=
  Γ.map (replaceParamWithVarFormula (σ := σ) (κ := κ) k a)

/-- Variable support of a Henkin context (all variables appearing anywhere in formulas). -/
def varsContext (Γ : List (FormulaH σ κ)) : Finset Var :=
  Γ.foldr (fun φ acc => varsFormula (σ := σ) (κ := κ) φ ∪ acc) ∅

@[simp] theorem varsContext_nil :
    varsContext (σ := σ) (κ := κ) ([] : List (FormulaH σ κ)) = ∅ := rfl

@[simp] theorem varsContext_cons (φ : FormulaH σ κ) (Γ : List (FormulaH σ κ)) :
    varsContext (σ := σ) (κ := κ) (φ :: Γ) =
      varsFormula (σ := σ) (κ := κ) φ ∪ varsContext (σ := σ) (κ := κ) Γ := by
  simp [varsContext]

theorem varsFormula_subset_varsContext_of_mem
    {Γ : List (FormulaH σ κ)} {φ : FormulaH σ κ}
    (hφ : φ ∈ Γ) :
    varsFormula (σ := σ) (κ := κ) φ ⊆ varsContext (σ := σ) (κ := κ) Γ := by
  induction Γ with
  | nil =>
      cases hφ
  | cons ψ Γ ih =>
      rcases List.mem_cons.1 hφ with hEq | hTail
      · subst hEq
        simp [varsContext_cons]
      ·
        have hSub : varsFormula (σ := σ) (κ := κ) φ ⊆ varsContext (σ := σ) (κ := κ) Γ :=
          ih hTail
        exact hSub.trans (by
          intro x hx
          exact Finset.mem_union.2 (Or.inr hx))

theorem not_mem_varsFormula_of_not_mem_varsContext_of_mem
    {Γ : List (FormulaH σ κ)} {φ : FormulaH σ κ} {b : Var}
    (hb : b ∉ varsContext (σ := σ) (κ := κ) Γ)
    (hφ : φ ∈ Γ) :
    b ∉ varsFormula (σ := σ) (κ := κ) φ := by
  intro hbφ
  exact hb (varsFormula_subset_varsContext_of_mem (σ := σ) (κ := κ) (Γ := Γ) (φ := φ) hφ hbφ)

/-- Free variables of a Henkin formula are included in its full variable support. -/
theorem fvFormula_subset_varsFormula
    (φ : FormulaH σ κ) :
    fvFormula (σ := σ) (κ := κ) φ ⊆ varsFormula (σ := σ) (κ := κ) φ := by
  intro x hx
  induction φ generalizing x with
  | top =>
      simp [fvFormula] at hx
  | bot =>
      simp [fvFormula] at hx
  | pred p args =>
      simpa [fvFormula, varsFormula] using hx
  | eExists t =>
      simpa [fvFormula, varsFormula] using hx
  | not φ ih =>
      exact ih (by simpa [fvFormula, varsFormula] using hx)
  | and φ ψ ihφ ihψ =>
      simp [fvFormula, varsFormula, Finset.mem_union] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (ihφ hx)
      · exact Or.inr (ihψ hx)
  | or φ ψ ihφ ihψ =>
      simp [fvFormula, varsFormula, Finset.mem_union] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (ihφ hx)
      · exact Or.inr (ihψ hx)
  | imp φ ψ ihφ ihψ =>
      simp [fvFormula, varsFormula, Finset.mem_union] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (ihφ hx)
      · exact Or.inr (ihψ hx)
  | sigma z φ ih =>
      have hx' : x ∈ fvFormula (σ := σ) (κ := κ) φ := (Finset.mem_erase.1 hx).2
      have : x ∈ varsFormula (σ := σ) (κ := κ) φ := ih hx'
      simpa [varsFormula] using (Finset.mem_insert_of_mem this)
  | pi z φ ih =>
      have hx' : x ∈ fvFormula (σ := σ) (κ := κ) φ := (Finset.mem_erase.1 hx).2
      have : x ∈ varsFormula (σ := σ) (κ := κ) φ := ih hx'
      simpa [varsFormula] using (Finset.mem_insert_of_mem this)

theorem not_mem_fvFormula_of_not_mem_varsContext_of_mem
    {Γ : List (FormulaH σ κ)} {φ : FormulaH σ κ} {b : Var}
    (hb : b ∉ varsContext (σ := σ) (κ := κ) Γ)
    (hφ : φ ∈ Γ) :
    b ∉ fvFormula (σ := σ) (κ := κ) φ := by
  intro hbφ
  exact not_mem_varsFormula_of_not_mem_varsContext_of_mem
    (σ := σ) (κ := κ) (Γ := Γ) (φ := φ) (b := b) hb hφ
    (fvFormula_subset_varsFormula (σ := σ) (κ := κ) φ hbφ)

/-- Free-variable context support is contained in full variable-context support. -/
theorem fvContext_subset_varsContext (Γ : List (FormulaH σ κ)) :
    fvContext (σ := σ) (κ := κ) Γ ⊆ varsContext (σ := σ) (κ := κ) Γ := by
  intro x hx
  rcases (mem_fvContext_iff (σ := σ) (κ := κ) (x := x) (Γ := Γ)).1 hx with ⟨ψ, hψΓ, hxψ⟩
  exact varsFormula_subset_varsContext_of_mem (σ := σ) (κ := κ) (Γ := Γ) (φ := ψ) hψΓ
    (fvFormula_subset_varsFormula (σ := σ) (κ := κ) ψ hxψ)

theorem fvContext_replaceParamWithVarContext_subset_insert
    [DecidableEq κ]
    (k : κ) (a : Var) (Γ : List (FormulaH σ κ)) :
    fvContext (σ := σ) (κ := κ)
      (replaceParamWithVarContext (σ := σ) (κ := κ) k a Γ) ⊆
      insert a (fvContext (σ := σ) (κ := κ) Γ) := by
  intro x hx
  induction Γ with
  | nil =>
      simp [replaceParamWithVarContext, fvContext] at hx
  | cons φ Γ ih =>
      simp [replaceParamWithVarContext, fvContext_cons, Finset.mem_union] at hx ⊢
      rcases hx with hx | hx
      ·
        have hx' :
            x ∈ insert a (fvFormula (σ := σ) (κ := κ) φ) :=
          fvFormula_replaceParamWithVarFormula_subset_insert
            (σ := σ) (κ := κ) k a φ hx
        rcases Finset.mem_insert.1 hx' with hEq | hMem
        · exact Or.inl hEq
        · exact Or.inr (Or.inl hMem)
      ·
        have hx' : x ∈ insert a (fvContext (σ := σ) (κ := κ) Γ) := ih hx
        rcases Finset.mem_insert.1 hx' with hEq | hMem
        · exact Or.inl hEq
        · exact Or.inr (Or.inr hMem)

theorem not_mem_fvContext_replaceParamWithVarContext_of_not_mem_fv_and_ne
    [DecidableEq κ]
    {a b : Var} {k : κ} {Γ : List (FormulaH σ κ)}
    (hb : b ∉ fvContext (σ := σ) (κ := κ) Γ)
    (hba : b ≠ a) :
    b ∉ fvContext (σ := σ) (κ := κ)
      (replaceParamWithVarContext (σ := σ) (κ := κ) k a Γ) := by
  intro hb'
  have hbIn :
      b ∈ insert a (fvContext (σ := σ) (κ := κ) Γ) :=
    fvContext_replaceParamWithVarContext_subset_insert (σ := σ) (κ := κ) k a Γ hb'
  rcases Finset.mem_insert.1 hbIn with hEq | hMem
  · exact hba hEq
  · exact hb hMem

/--
Variable-support control after rewriting a distinguished parameter to a variable across a context.
-/
theorem varsContext_replaceParamWithVarContext_subset_insert
    [DecidableEq κ]
    (k : κ) (a : Var) (Γ : List (FormulaH σ κ)) :
    varsContext (σ := σ) (κ := κ)
      (replaceParamWithVarContext (σ := σ) (κ := κ) k a Γ) ⊆
      insert a (varsContext (σ := σ) (κ := κ) Γ) := by
  intro x hx
  induction Γ with
  | nil =>
      simp [replaceParamWithVarContext, varsContext] at hx
  | cons φ Γ ih =>
      simp [replaceParamWithVarContext, varsContext_cons, Finset.mem_union] at hx ⊢
      rcases hx with hx | hx
      ·
        have hx' :
            x ∈ insert a (varsFormula (σ := σ) (κ := κ) φ) :=
          varsFormula_replaceParamWithVarFormula_subset_insert
            (σ := σ) (κ := κ) k a φ hx
        rcases Finset.mem_insert.1 hx' with hEq | hMem
        · exact Or.inl hEq
        · exact Or.inr (Or.inl hMem)
      ·
        have hx' : x ∈ insert a (varsContext (σ := σ) (κ := κ) Γ) := ih hx
        rcases Finset.mem_insert.1 hx' with hEq | hMem
        · exact Or.inl hEq
        · exact Or.inr (Or.inr hMem)

theorem not_mem_varsContext_replaceParamWithVarContext_of_not_mem_and_ne
    [DecidableEq κ]
    {a b : Var} {k : κ} {Γ : List (FormulaH σ κ)}
    (hb : b ∉ varsContext (σ := σ) (κ := κ) Γ)
    (hba : b ≠ a) :
    b ∉ varsContext (σ := σ) (κ := κ)
      (replaceParamWithVarContext (σ := σ) (κ := κ) k a Γ) := by
  intro hb'
  have hbIn :
      b ∈ insert a (varsContext (σ := σ) (κ := κ) Γ) :=
    varsContext_replaceParamWithVarContext_subset_insert (σ := σ) (κ := κ) k a Γ hb'
  rcases Finset.mem_insert.1 hbIn with hEq | hMem
  · exact hba hEq
  · exact hb hMem

theorem not_mem_fvContext_replaceParamWithVarContext_of_not_mem_and_ne
    [DecidableEq κ]
    {a b : Var} {k : κ} {Γ : List (FormulaH σ κ)}
    (hb : b ∉ varsContext (σ := σ) (κ := κ) Γ)
    (hba : b ≠ a) :
    b ∉ fvContext (σ := σ) (κ := κ)
      (replaceParamWithVarContext (σ := σ) (κ := κ) k a Γ) := by
  intro hb'
  exact not_mem_varsContext_replaceParamWithVarContext_of_not_mem_and_ne
    (σ := σ) (κ := κ) (a := a) (b := b) (k := k) (Γ := Γ) hb hba
    ((fvContext_subset_varsContext (σ := σ) (κ := κ)
      (replaceParamWithVarContext (σ := σ) (κ := κ) k a Γ)) hb')

theorem not_mem_varsFormula_of_not_mem_varsContext_replaceParam_of_mem
    [DecidableEq κ]
    {a b : Var} {k : κ} {Γ : List (FormulaH σ κ)} {ψ : FormulaH σ κ}
    (hb : b ∉ varsContext (σ := σ) (κ := κ) Γ)
    (hba : b ≠ a)
    (hψ : ψ ∈ replaceParamWithVarContext (σ := σ) (κ := κ) k a Γ) :
    b ∉ varsFormula (σ := σ) (κ := κ) ψ := by
  have hbCtx :
      b ∉ varsContext (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Γ) :=
    not_mem_varsContext_replaceParamWithVarContext_of_not_mem_and_ne
      (σ := σ) (κ := κ) (a := a) (b := b) (k := k) (Γ := Γ) hb hba
  exact not_mem_varsFormula_of_not_mem_varsContext_of_mem
    (σ := σ) (κ := κ)
    (Γ := replaceParamWithVarContext (σ := σ) (κ := κ) k a Γ)
    (φ := ψ) (b := b) hbCtx hψ

theorem not_mem_fvFormula_of_not_mem_varsContext_replaceParam_of_mem
    [DecidableEq κ]
    {a b : Var} {k : κ} {Γ : List (FormulaH σ κ)} {ψ : FormulaH σ κ}
    (hb : b ∉ varsContext (σ := σ) (κ := κ) Γ)
    (hba : b ≠ a)
    (hψ : ψ ∈ replaceParamWithVarContext (σ := σ) (κ := κ) k a Γ) :
    b ∉ fvFormula (σ := σ) (κ := κ) ψ := by
  intro hbψ
  exact not_mem_varsFormula_of_not_mem_varsContext_replaceParam_of_mem
    (σ := σ) (κ := κ) (a := a) (b := b) (k := k) (Γ := Γ) (ψ := ψ)
    hb hba hψ (fvFormula_subset_varsFormula (σ := σ) (κ := κ) ψ hbψ)

/--
Finite variable support extractor for `NDH.Derives`.

This is a minimal support object used to choose fresh variables in Track A:
it covers the ambient context and goal.
-/
theorem exists_varsDerives_support
    {Γ : List (FormulaH σ κ)} {φ : FormulaH σ κ}
    (_h : Derives (σ := σ) (κ := κ) Γ φ) :
    ∃ E : Finset Var,
      varsContext (σ := σ) (κ := κ) Γ ⊆ E ∧
      varsFormula (σ := σ) (κ := κ) φ ⊆ E := by
  refine ⟨varsContext (σ := σ) (κ := κ) Γ ∪ varsFormula (σ := σ) (κ := κ) φ, ?_, ?_⟩
  · intro x hx
    exact Finset.mem_union.2 (Or.inl hx)
  · intro x hx
    exact Finset.mem_union.2 (Or.inr hx)

/--
Fresh-variable corollary for the support extracted above.

Produces a variable avoiding both the context-support and the goal-support.
-/
theorem exists_freshVar_not_mem_varsDerives_support
    {Γ : List (FormulaH σ κ)} {φ : FormulaH σ κ}
    (h : Derives (σ := σ) (κ := κ) Γ φ) :
    ∃ a : Var,
      a ∉ varsContext (σ := σ) (κ := κ) Γ ∧
      a ∉ varsFormula (σ := σ) (κ := κ) φ := by
  rcases exists_varsDerives_support (σ := σ) (κ := κ) (Γ := Γ) (φ := φ) h with
    ⟨E, hΓE, hφE⟩
  refine ⟨Syntax.freshVar E, ?_, ?_⟩
  · intro hmem
    exact Syntax.freshVar_not_mem E (hΓE hmem)
  · intro hmem
    exact Syntax.freshVar_not_mem E (hφE hmem)

/--
Sigma-side-condition freshness extractor.

Given a derivation context `Γ` and formulas `body`, `goal`, choose a variable fresh for:
`fvContext Γ`, `varsFormula body`, and `fvFormula goal`.
-/
theorem exists_fresh_for_sigma_side_conditions
    (Γ : List (FormulaH σ κ))
    (body goal : FormulaH σ κ) :
    ∃ a : Var,
      a ∉ fvContext (σ := σ) (κ := κ) Γ ∧
      a ∉ varsFormula (σ := σ) (κ := κ) body ∧
      a ∉ fvFormula (σ := σ) (κ := κ) goal := by
  let avoid : Finset Var :=
    (varsContext (σ := σ) (κ := κ) Γ ∪ varsFormula (σ := σ) (κ := κ) body) ∪
      varsFormula (σ := σ) (κ := κ) goal
  refine ⟨Syntax.freshVar avoid, ?_, ?_, ?_⟩
  ·
    intro hmem
    have hInVarsCtx : Syntax.freshVar avoid ∈ varsContext (σ := σ) (κ := κ) Γ :=
      (fvContext_subset_varsContext (σ := σ) (κ := κ) Γ) hmem
    exact Syntax.freshVar_not_mem avoid (by
      exact Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl hInVarsCtx))))
  ·
    intro hmem
    exact Syntax.freshVar_not_mem avoid (by
      exact Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inr hmem))))
  ·
    intro hmem
    have hInVars : Syntax.freshVar avoid ∈ varsFormula (σ := σ) (κ := κ) goal :=
      fvFormula_subset_varsFormula (σ := σ) (κ := κ) goal hmem
    exact Syntax.freshVar_not_mem avoid (by
      exact Finset.mem_union.2 (Or.inr hInVars))

/--
Sigma-side-condition freshness extractor with explicit disequalities.

Chooses `b` fresh for `fvContext Γ`, `varsFormula body`, `fvFormula goal`, and also distinct
from designated variables `a` and `x`.
-/
theorem exists_fresh_for_sigma_side_conditions_and_ne
    (Γ : List (FormulaH σ κ))
    (body goal : FormulaH σ κ)
    (a x : Var) :
    ∃ b : Var,
      b ≠ a ∧
      b ≠ x ∧
      b ∉ fvContext (σ := σ) (κ := κ) Γ ∧
      b ∉ varsFormula (σ := σ) (κ := κ) body ∧
      b ∉ fvFormula (σ := σ) (κ := κ) goal := by
  let avoid : Finset Var :=
    insert x (insert a
      ((varsContext (σ := σ) (κ := κ) Γ ∪ varsFormula (σ := σ) (κ := κ) body) ∪
        varsFormula (σ := σ) (κ := κ) goal))
  refine ⟨Syntax.freshVar avoid, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro hEq
    have hInA : a ∈ avoid := by
      simp [avoid]
    have hIn : Syntax.freshVar avoid ∈ avoid := by
      simpa [hEq] using hInA
    exact Syntax.freshVar_not_mem avoid hIn
  ·
    intro hEq
    have hInX : x ∈ avoid := by
      simp [avoid]
    have hIn : Syntax.freshVar avoid ∈ avoid := by
      simpa [hEq] using hInX
    exact Syntax.freshVar_not_mem avoid hIn
  ·
    intro hmem
    have hInVarsCtx : Syntax.freshVar avoid ∈ varsContext (σ := σ) (κ := κ) Γ :=
      (fvContext_subset_varsContext (σ := σ) (κ := κ) Γ) hmem
    exact Syntax.freshVar_not_mem avoid (by
      exact Finset.mem_insert.2 (Or.inr (Finset.mem_insert.2
        (Or.inr (Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl hInVarsCtx))))))))
  ·
    intro hmem
    exact Syntax.freshVar_not_mem avoid (by
      exact Finset.mem_insert.2 (Or.inr (Finset.mem_insert.2
        (Or.inr (Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inr hmem))))))))
  ·
    intro hmem
    have hInVars : Syntax.freshVar avoid ∈ varsFormula (σ := σ) (κ := κ) goal :=
      fvFormula_subset_varsFormula (σ := σ) (κ := κ) goal hmem
    exact Syntax.freshVar_not_mem avoid (by
      exact Finset.mem_insert.2 (Or.inr (Finset.mem_insert.2
        (Or.inr (Finset.mem_union.2 (Or.inr hInVars))))))

/--
Fresh-variable chooser for sigma-side conditions after param→var context/formula rewriting.

This packages the exact freshness obligations used by Track A transports on rewritten judgments.
-/
theorem exists_fresh_for_sigma_side_conditions_replaceParam
    [DecidableEq κ]
    (k : κ) (a : Var)
    (Γ : List (FormulaH σ κ))
    (body goal : FormulaH σ κ) :
    ∃ b : Var,
      b ≠ a ∧
      b ∉ fvContext (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Γ) ∧
      b ∉ varsFormula (σ := σ) (κ := κ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a body) ∧
      b ∉ fvFormula (σ := σ) (κ := κ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a goal) := by
  let avoid : Finset Var :=
    insert a
      ((varsContext (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Γ) ∪
        varsFormula (σ := σ) (κ := κ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a body)) ∪
        varsFormula (σ := σ) (κ := κ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a goal))
  refine ⟨Syntax.freshVar avoid, ?_, ?_, ?_, ?_⟩
  ·
    intro hEq
    have hInA : a ∈ avoid := by
      simp [avoid]
    have hIn : Syntax.freshVar avoid ∈ avoid := by
      simpa [hEq] using hInA
    exact Syntax.freshVar_not_mem avoid hIn
  ·
    intro hmem
    have hInVars :
        Syntax.freshVar avoid ∈
          varsContext (σ := σ) (κ := κ)
            (replaceParamWithVarContext (σ := σ) (κ := κ) k a Γ) :=
      (fvContext_subset_varsContext (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Γ)) hmem
    exact Syntax.freshVar_not_mem avoid (by
      exact Finset.mem_insert.2 (Or.inr (Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl hInVars))))))
  ·
    intro hmem
    exact Syntax.freshVar_not_mem avoid (by
      exact Finset.mem_insert.2 (Or.inr (Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inr hmem))))))
  ·
    intro hmem
    have hInVars :
        Syntax.freshVar avoid ∈
          varsFormula (σ := σ) (κ := κ)
            (replaceParamWithVarFormula (σ := σ) (κ := κ) k a goal) :=
      fvFormula_subset_varsFormula (σ := σ) (κ := κ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a goal) hmem
    exact Syntax.freshVar_not_mem avoid (by
      exact Finset.mem_insert.2 (Or.inr (Finset.mem_union.2 (Or.inr hInVars))))

/--
Fresh-variable chooser for sigma-side conditions after param→var rewriting, additionally
avoiding a designated variable `x`.

This is useful when a transport step needs both `b ≠ a` and `b ≠ x` side-conditions.
-/
theorem exists_fresh_for_sigma_side_conditions_replaceParam_and_ne
    [DecidableEq κ]
    (k : κ) (a x : Var)
    (Γ : List (FormulaH σ κ))
    (body goal : FormulaH σ κ) :
    ∃ b : Var,
      b ≠ a ∧
      b ≠ x ∧
      b ∉ fvContext (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Γ) ∧
      b ∉ varsFormula (σ := σ) (κ := κ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a body) ∧
      b ∉ fvFormula (σ := σ) (κ := κ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a goal) := by
  let avoid : Finset Var :=
    insert x (insert a
      ((varsContext (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Γ) ∪
        varsFormula (σ := σ) (κ := κ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a body)) ∪
        varsFormula (σ := σ) (κ := κ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a goal)))
  refine ⟨Syntax.freshVar avoid, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro hEq
    have hInA : a ∈ avoid := by
      simp [avoid]
    have hIn : Syntax.freshVar avoid ∈ avoid := by
      simpa [hEq] using hInA
    exact Syntax.freshVar_not_mem avoid hIn
  ·
    intro hEq
    have hInX : x ∈ avoid := by
      simp [avoid]
    have hIn : Syntax.freshVar avoid ∈ avoid := by
      simpa [hEq] using hInX
    exact Syntax.freshVar_not_mem avoid hIn
  ·
    intro hmem
    have hInVars :
        Syntax.freshVar avoid ∈
          varsContext (σ := σ) (κ := κ)
            (replaceParamWithVarContext (σ := σ) (κ := κ) k a Γ) :=
      (fvContext_subset_varsContext (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Γ)) hmem
    exact Syntax.freshVar_not_mem avoid (by
      exact Finset.mem_insert.2 (Or.inr (Finset.mem_insert.2
        (Or.inr (Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl hInVars))))))))
  ·
    intro hmem
    exact Syntax.freshVar_not_mem avoid (by
      exact Finset.mem_insert.2 (Or.inr (Finset.mem_insert.2
        (Or.inr (Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inr hmem))))))))
  ·
    intro hmem
    have hInVars :
        Syntax.freshVar avoid ∈
          varsFormula (σ := σ) (κ := κ)
            (replaceParamWithVarFormula (σ := σ) (κ := κ) k a goal) :=
      fvFormula_subset_varsFormula (σ := σ) (κ := κ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a goal) hmem
    exact Syntax.freshVar_not_mem avoid (by
      exact Finset.mem_insert.2 (Or.inr (Finset.mem_insert.2
        (Or.inr (Finset.mem_union.2 (Or.inr hInVars))))))

end NDH
end Noneism
end HeytingLean
