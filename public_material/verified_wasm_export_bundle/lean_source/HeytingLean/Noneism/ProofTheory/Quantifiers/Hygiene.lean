import HeytingLean.Noneism.ProofTheory.ND

/-!
# Noneism.ProofTheory.Quantifiers.Hygiene

This module collects **syntax-side** facts that make the `sigma/pi` natural-deduction rules in
`Noneism.ProofTheory.ND` genuinely hygienic (capture-avoiding), so we can later add standard
`∀/∃`-style derived rules without relying on informal binder reasoning.

Key points:
- `Syntax.substFormula` is capture-avoiding and will alpha-rename binder variables *only* when it
  would otherwise capture a variable occurring free in the substituted term.
- The ND quantifier instantiation rules track freshness against binder names (`boundVars`) to
  prevent alpha-renaming branches during substitution.
- We also record simple relations between `fvFormula` and `varsFormula` used by eigenvariable side
  conditions.
-/

namespace HeytingLean
namespace Noneism

open scoped Classical

open Formula

namespace Syntax

/-! ## `fvFormula` is contained in `varsFormula` -/

theorem fvFormula_subset_varsFormula {σ : Type} :
    ∀ φ : Formula σ, fvFormula φ ⊆ varsFormula φ := by
  intro φ
  induction φ with
  | top => simp [fvFormula, varsFormula]
  | bot => simp [fvFormula, varsFormula]
  | pred p args => simp [fvFormula, varsFormula]
  | eExists t => simp [fvFormula, varsFormula]
  | not φ ih =>
      simpa [fvFormula, varsFormula] using ih
  | and φ ψ ihφ ihψ =>
      intro x hx
      simp [fvFormula, varsFormula, Finset.mem_union] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (ihφ hx)
      · exact Or.inr (ihψ hx)
  | or φ ψ ihφ ihψ =>
      intro x hx
      simp [fvFormula, varsFormula, Finset.mem_union] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (ihφ hx)
      · exact Or.inr (ihψ hx)
  | imp φ ψ ihφ ihψ =>
      intro x hx
      simp [fvFormula, varsFormula, Finset.mem_union] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (ihφ hx)
      · exact Or.inr (ihψ hx)
  | sigma z φ ih =>
      intro x hx
      -- `x ∈ erase z (fvFormula φ)` implies `x ∈ fvFormula φ`, then use IH and `mem_insert`.
      have hx' : x ∈ fvFormula φ := (Finset.mem_erase.1 hx).2
      have : x ∈ varsFormula φ := ih hx'
      -- `varsFormula (sigma z φ) = insert z (varsFormula φ)`
      simpa [varsFormula] using (Finset.mem_insert_of_mem this)
  | pi z φ ih =>
      intro x hx
      have hx' : x ∈ fvFormula φ := (Finset.mem_erase.1 hx).2
      have : x ∈ varsFormula φ := ih hx'
      simpa [varsFormula] using (Finset.mem_insert_of_mem this)

theorem boundVars_subset_varsFormula {σ : Type} :
    ∀ φ : Formula σ, boundVars (σ := σ) φ ⊆ varsFormula (σ := σ) φ := by
  intro φ
  induction φ with
  | top => simp [boundVars, varsFormula]
  | bot => simp [boundVars, varsFormula]
  | pred p args => simp [boundVars, varsFormula]
  | eExists t => simp [boundVars, varsFormula]
  | not φ ih =>
      simpa [boundVars, varsFormula] using ih
  | and φ ψ ihφ ihψ =>
      intro x hx
      simp [boundVars, varsFormula, Finset.mem_union] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (ihφ hx)
      · exact Or.inr (ihψ hx)
  | or φ ψ ihφ ihψ =>
      intro x hx
      simp [boundVars, varsFormula, Finset.mem_union] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (ihφ hx)
      · exact Or.inr (ihψ hx)
  | imp φ ψ ihφ ihψ =>
      intro x hx
      simp [boundVars, varsFormula, Finset.mem_union] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (ihφ hx)
      · exact Or.inr (ihψ hx)
  | sigma z φ ih =>
      intro x hx
      rcases Finset.mem_insert.1 hx with hEq | hx'
      · subst x
        simp [varsFormula]
      ·
        have : x ∈ varsFormula (σ := σ) φ := ih hx'
        simpa [varsFormula] using (Finset.mem_insert_of_mem this)
  | pi z φ ih =>
      intro x hx
      rcases Finset.mem_insert.1 hx with hEq | hx'
      · subst x
        simp [varsFormula]
      ·
        have : x ∈ varsFormula (σ := σ) φ := ih hx'
        simpa [varsFormula] using (Finset.mem_insert_of_mem this)

theorem not_mem_fvFormula_of_not_mem_varsFormula {σ : Type} {a : Var} {φ : Formula σ}
    (ha : a ∉ varsFormula φ) : a ∉ fvFormula φ := by
  intro hafv
  exact ha (fvFormula_subset_varsFormula (σ := σ) φ hafv)

theorem not_mem_boundVars_of_not_mem_varsFormula {σ : Type} {a : Var} {φ : Formula σ}
    (ha : a ∉ varsFormula (σ := σ) φ) : a ∉ boundVars (σ := σ) φ := by
  intro hab
  exact ha (boundVars_subset_varsFormula (σ := σ) φ hab)

theorem not_mem_fvFormula_of_not_mem_fvContext {σ : Type} {Γ : List (Formula σ)} {a : Var}
    (ha : a ∉ ND.fvContext (σ := σ) Γ) :
    ∀ {ψ : Formula σ}, ψ ∈ Γ → a ∉ fvFormula ψ := by
  intro ψ hψ
  induction Γ with
  | nil =>
      cases hψ
  | cons φ Γ ih =>
      have hsplit : a ∉ fvFormula φ ∧ a ∉ ND.fvContext (σ := σ) Γ := by
        have : a ∉ fvFormula φ ∪ ND.fvContext (σ := σ) Γ := by
          simpa [ND.fvContext] using ha
        simpa [Finset.mem_union] using this
      rcases List.mem_cons.1 hψ with hEq | hMem
      · subst ψ
        exact hsplit.1
      · exact ih hsplit.2 hMem

/-! ## Specialization: `x ↦ var a` does not alpha-rename under eigenvariable conditions -/

lemma substFormula_sigma_var_of_not_mem_boundVars {σ : Type}
    (x a z : Var) (φ : Formula σ)
    (ha : a ∉ boundVars (σ := σ) (.sigma z φ)) :
    substFormula (σ := σ) x (.var a) (.sigma z φ) =
      if z = x then
        (.sigma z φ)
      else
        (.sigma z (substFormula (σ := σ) x (.var a) φ)) := by
  classical
  by_cases hz : z = x
  · simp [substFormula, hz]
  ·
    have hIns : a ∉ insert z (boundVars (σ := σ) φ) := by
      simpa [boundVars] using ha
    have haz : a ≠ z := by
      intro hEq
      apply hIns
      simp [hEq]
    have hzfv : z ∉ fvTerm (.var a) := by
      -- `fvTerm (var a) = {a}`.
      simpa [fvTerm] using haz.symm
    simp [substFormula, hz, hzfv]

lemma substFormula_pi_var_of_not_mem_boundVars {σ : Type}
    (x a z : Var) (φ : Formula σ)
    (ha : a ∉ boundVars (σ := σ) (.pi z φ)) :
    substFormula (σ := σ) x (.var a) (.pi z φ) =
      if z = x then
        (.pi z φ)
      else
        (.pi z (substFormula (σ := σ) x (.var a) φ)) := by
  classical
  by_cases hz : z = x
  · simp [substFormula, hz]
  ·
    have hIns : a ∉ insert z (boundVars (σ := σ) φ) := by
      simpa [boundVars] using ha
    have haz : a ≠ z := by
      intro hEq
      apply hIns
      simp [hEq]
    have hzfv : z ∉ fvTerm (.var a) := by
      simpa [fvTerm] using haz.symm
    simp [substFormula, hz, hzfv]

lemma substFormula_sigma_var_of_not_mem_varsFormula {σ : Type}
    (x a z : Var) (φ : Formula σ)
    (ha : a ∉ varsFormula (σ := σ) (.sigma z φ)) :
    substFormula (σ := σ) x (.var a) (.sigma z φ) =
      if z = x then
        (.sigma z φ)
      else
        (.sigma z (substFormula (σ := σ) x (.var a) φ)) := by
  exact substFormula_sigma_var_of_not_mem_boundVars (σ := σ) x a z φ
    (not_mem_boundVars_of_not_mem_varsFormula (σ := σ) ha)

lemma substFormula_pi_var_of_not_mem_varsFormula {σ : Type}
    (x a z : Var) (φ : Formula σ)
    (ha : a ∉ varsFormula (σ := σ) (.pi z φ)) :
    substFormula (σ := σ) x (.var a) (.pi z φ) =
      if z = x then
        (.pi z φ)
      else
        (.pi z (substFormula (σ := σ) x (.var a) φ)) := by
  exact substFormula_pi_var_of_not_mem_boundVars (σ := σ) x a z φ
    (not_mem_boundVars_of_not_mem_varsFormula (σ := σ) ha)

/-! ## Global "no alpha-renaming" specialization for `x ↦ var a` -/

/--
Substitution specialized to variable terms, assuming no alpha-renaming branch is taken.

This is the structurally recursive form expected when `a` avoids bound-variable capture in `φ`.
-/
def substFormulaVarNoAlpha {σ : Type} (x a : Var) : Formula σ → Formula σ
  | .top => .top
  | .bot => .bot
  | .pred p args => .pred p (substTerms x (.var a) args)
  | .eExists t => .eExists (substTerm x (.var a) t)
  | .not φ => .not (substFormulaVarNoAlpha x a φ)
  | .and φ ψ => .and (substFormulaVarNoAlpha x a φ) (substFormulaVarNoAlpha x a ψ)
  | .or φ ψ => .or (substFormulaVarNoAlpha x a φ) (substFormulaVarNoAlpha x a ψ)
  | .imp φ ψ => .imp (substFormulaVarNoAlpha x a φ) (substFormulaVarNoAlpha x a ψ)
  | .sigma z φ =>
      if z = x then
        .sigma z φ
      else
        .sigma z (substFormulaVarNoAlpha x a φ)
  | .pi z φ =>
      if z = x then
        .pi z φ
      else
        .pi z (substFormulaVarNoAlpha x a φ)

/--
If `a` is absent from all variables of `φ`, capture-avoiding substitution
`substFormula x (var a) φ` never triggers alpha-renaming and equals the direct structural
specialization `substFormulaVarNoAlpha x a φ`.
-/
lemma substFormula_var_eq_noAlpha_of_not_mem_boundVars {σ : Type}
    (x a : Var) :
    ∀ φ : Formula σ,
      a ∉ boundVars (σ := σ) φ →
        substFormula (σ := σ) x (.var a) φ = substFormulaVarNoAlpha (σ := σ) x a φ := by
  intro φ
  induction φ with
  | top =>
      intro _
      simp [substFormula, substFormulaVarNoAlpha]
  | bot =>
      intro _
      simp [substFormula, substFormulaVarNoAlpha]
  | pred p args =>
      intro _
      simp [substFormula, substFormulaVarNoAlpha]
  | eExists t =>
      intro _
      simp [substFormula, substFormulaVarNoAlpha]
  | not φ ih =>
      intro ha
      simpa [substFormula, substFormulaVarNoAlpha, boundVars] using
        congrArg Formula.not (ih (by simpa [boundVars] using ha))
  | and φ ψ ihφ ihψ =>
      intro ha
      have ha' : a ∉ boundVars (σ := σ) φ ∧ a ∉ boundVars (σ := σ) ψ := by
        simpa [boundVars, Finset.mem_union] using ha
      simpa [substFormula, substFormulaVarNoAlpha] using
        congrArg₂ Formula.and (ihφ ha'.1) (ihψ ha'.2)
  | or φ ψ ihφ ihψ =>
      intro ha
      have ha' : a ∉ boundVars (σ := σ) φ ∧ a ∉ boundVars (σ := σ) ψ := by
        simpa [boundVars, Finset.mem_union] using ha
      simpa [substFormula, substFormulaVarNoAlpha] using
        congrArg₂ Formula.or (ihφ ha'.1) (ihψ ha'.2)
  | imp φ ψ ihφ ihψ =>
      intro ha
      have ha' : a ∉ boundVars (σ := σ) φ ∧ a ∉ boundVars (σ := σ) ψ := by
        simpa [boundVars, Finset.mem_union] using ha
      simpa [substFormula, substFormulaVarNoAlpha] using
        congrArg₂ Formula.imp (ihφ ha'.1) (ihψ ha'.2)
  | sigma z φ ih =>
      intro ha
      by_cases hz : z = x
      · simp [substFormula, substFormulaVarNoAlpha, hz]
      ·
        have hsplit : a ≠ z ∧ a ∉ boundVars (σ := σ) φ := by
          simpa [boundVars, Finset.mem_insert, Finset.mem_union] using ha
        have hzfv : z ∉ fvTerm (.var a) := by
          have hza : z ≠ a := hsplit.1.symm
          simp [fvTerm, hza]
        simp [substFormula, substFormulaVarNoAlpha, hz, hzfv, ih hsplit.2]
  | pi z φ ih =>
      intro ha
      by_cases hz : z = x
      · simp [substFormula, substFormulaVarNoAlpha, hz]
      ·
        have hsplit : a ≠ z ∧ a ∉ boundVars (σ := σ) φ := by
          simpa [boundVars, Finset.mem_insert, Finset.mem_union] using ha
        have hzfv : z ∉ fvTerm (.var a) := by
          have hza : z ≠ a := hsplit.1.symm
          simp [fvTerm, hza]
        simp [substFormula, substFormulaVarNoAlpha, hz, hzfv, ih hsplit.2]

lemma substFormula_var_eq_noAlpha_of_not_mem_varsFormula {σ : Type}
    (x a : Var) :
    ∀ φ : Formula σ,
      a ∉ varsFormula (σ := σ) φ →
        substFormula (σ := σ) x (.var a) φ = substFormulaVarNoAlpha (σ := σ) x a φ := by
  intro φ ha
  exact substFormula_var_eq_noAlpha_of_not_mem_boundVars (σ := σ) x a φ
    (not_mem_boundVars_of_not_mem_varsFormula (σ := σ) ha)

lemma not_mem_fvTerm_substTerm_var_of_not_mem_fvTerm (x a b : Var) :
    ∀ t : Term,
      a ∉ fvTerm t →
      a ≠ b →
      a ∉ fvTerm (substTerm x (.var b) t) := by
  intro t ha hab
  cases t with
  | var z =>
      have haz : a ≠ z := by
        intro hEq
        apply ha
        simp [fvTerm, hEq]
      by_cases hzx : z = x
      · subst hzx
        simp [substTerm, fvTerm, hab]
      · simp [substTerm, fvTerm, hzx, haz]

lemma not_mem_fvTerms_substTerms_var_of_not_mem_fvTerms (x a b : Var) :
    ∀ ts : List Term,
      a ∉ fvTerms ts →
      a ≠ b →
      a ∉ fvTerms (substTerms x (.var b) ts) := by
  intro ts
  induction ts with
  | nil =>
      intro _ _
      simp [fvTerms, substTerms]
  | cons t ts ih =>
      intro ha hab
      have hsplit : a ∉ fvTerm t ∧ a ∉ fvTerms ts := by
        simpa [fvTerms, Finset.mem_union] using ha
      intro hmem
      have hsplit' :
          a ∈ fvTerm (substTerm x (.var b) t) ∨
            a ∈ fvTerms (substTerms x (.var b) ts) := by
        simpa [fvTerms, substTerms, Finset.mem_union] using hmem
      rcases hsplit' with hhead | htail
      · exact (not_mem_fvTerm_substTerm_var_of_not_mem_fvTerm x a b t hsplit.1 hab) hhead
      · exact (ih hsplit.2 hab) htail

lemma not_mem_fvFormula_substFormulaVarNoAlpha_of_not_mem_varsFormula {σ : Type}
    (x a b : Var) :
    ∀ φ : Formula σ,
      a ∉ varsFormula (σ := σ) φ →
      a ≠ b →
      a ∉ fvFormula (σ := σ) (substFormulaVarNoAlpha (σ := σ) x b φ) := by
  intro φ
  induction φ with
  | top =>
      intro _ _
      simp [substFormulaVarNoAlpha, fvFormula]
  | bot =>
      intro _ _
      simp [substFormulaVarNoAlpha, fvFormula]
  | pred p args =>
      intro ha hab
      exact
        not_mem_fvTerms_substTerms_var_of_not_mem_fvTerms x a b args
          (by simpa [varsFormula] using ha)
          hab
  | eExists t =>
      intro ha hab
      exact
        not_mem_fvTerm_substTerm_var_of_not_mem_fvTerm x a b t
          (by simpa [varsFormula] using ha)
          hab
  | not φ ih =>
      intro ha hab
      exact ih (by simpa [varsFormula] using ha) hab
  | and φ ψ ihφ ihψ =>
      intro ha hab
      have hsplit : a ∉ varsFormula (σ := σ) φ ∧ a ∉ varsFormula (σ := σ) ψ := by
        simpa [varsFormula, Finset.mem_union] using ha
      intro hafv
      have hsplitFv : a ∈ fvFormula (σ := σ) (substFormulaVarNoAlpha (σ := σ) x b φ) ∨
          a ∈ fvFormula (σ := σ) (substFormulaVarNoAlpha (σ := σ) x b ψ) := by
        simpa [substFormulaVarNoAlpha, fvFormula, Finset.mem_union] using hafv
      rcases hsplitFv with hφ | hψ
      · exact ihφ hsplit.1 hab hφ
      · exact ihψ hsplit.2 hab hψ
  | or φ ψ ihφ ihψ =>
      intro ha hab
      have hsplit : a ∉ varsFormula (σ := σ) φ ∧ a ∉ varsFormula (σ := σ) ψ := by
        simpa [varsFormula, Finset.mem_union] using ha
      intro hafv
      have hsplitFv : a ∈ fvFormula (σ := σ) (substFormulaVarNoAlpha (σ := σ) x b φ) ∨
          a ∈ fvFormula (σ := σ) (substFormulaVarNoAlpha (σ := σ) x b ψ) := by
        simpa [substFormulaVarNoAlpha, fvFormula, Finset.mem_union] using hafv
      rcases hsplitFv with hφ | hψ
      · exact ihφ hsplit.1 hab hφ
      · exact ihψ hsplit.2 hab hψ
  | imp φ ψ ihφ ihψ =>
      intro ha hab
      have hsplit : a ∉ varsFormula (σ := σ) φ ∧ a ∉ varsFormula (σ := σ) ψ := by
        simpa [varsFormula, Finset.mem_union] using ha
      intro hafv
      have hsplitFv : a ∈ fvFormula (σ := σ) (substFormulaVarNoAlpha (σ := σ) x b φ) ∨
          a ∈ fvFormula (σ := σ) (substFormulaVarNoAlpha (σ := σ) x b ψ) := by
        simpa [substFormulaVarNoAlpha, fvFormula, Finset.mem_union] using hafv
      rcases hsplitFv with hφ | hψ
      · exact ihφ hsplit.1 hab hφ
      · exact ihψ hsplit.2 hab hψ
  | sigma z φ ih =>
      intro ha hab
      by_cases hzx : z = x
      ·
        have hsplit : a ≠ z ∧ a ∉ varsFormula (σ := σ) φ := by
          simpa [varsFormula, Finset.mem_insert, Finset.mem_union] using ha
        intro hafv
        have hafv' : a ∈ (fvFormula (σ := σ) φ).erase z := by
          simpa [substFormulaVarNoAlpha, fvFormula, hzx] using hafv
        have hafvBody : a ∈ fvFormula (σ := σ) φ := by
          exact (Finset.mem_erase.1 hafv').2
        exact (not_mem_fvFormula_of_not_mem_varsFormula (σ := σ) (a := a) (φ := φ) hsplit.2) hafvBody
      ·
        have hsplit : a ≠ z ∧ a ∉ varsFormula (σ := σ) φ := by
          simpa [varsFormula, Finset.mem_insert, Finset.mem_union] using ha
        intro hafv
        have hafv' :
            a ∈ (fvFormula (σ := σ) (substFormulaVarNoAlpha (σ := σ) x b φ)).erase z := by
          simpa [substFormulaVarNoAlpha, fvFormula, hzx] using hafv
        have hafvBody : a ∈ fvFormula (σ := σ) (substFormulaVarNoAlpha (σ := σ) x b φ) := by
          exact (Finset.mem_erase.1 hafv').2
        exact ih hsplit.2 hab hafvBody
  | pi z φ ih =>
      intro ha hab
      by_cases hzx : z = x
      ·
        have hsplit : a ≠ z ∧ a ∉ varsFormula (σ := σ) φ := by
          simpa [varsFormula, Finset.mem_insert, Finset.mem_union] using ha
        intro hafv
        have hafv' : a ∈ (fvFormula (σ := σ) φ).erase z := by
          simpa [substFormulaVarNoAlpha, fvFormula, hzx] using hafv
        have hafvBody : a ∈ fvFormula (σ := σ) φ := by
          exact (Finset.mem_erase.1 hafv').2
        exact (not_mem_fvFormula_of_not_mem_varsFormula (σ := σ) (a := a) (φ := φ) hsplit.2) hafvBody
      ·
        have hsplit : a ≠ z ∧ a ∉ varsFormula (σ := σ) φ := by
          simpa [varsFormula, Finset.mem_insert, Finset.mem_union] using ha
        intro hafv
        have hafv' :
            a ∈ (fvFormula (σ := σ) (substFormulaVarNoAlpha (σ := σ) x b φ)).erase z := by
          simpa [substFormulaVarNoAlpha, fvFormula, hzx] using hafv
        have hafvBody : a ∈ fvFormula (σ := σ) (substFormulaVarNoAlpha (σ := σ) x b φ) := by
          exact (Finset.mem_erase.1 hafv').2
        exact ih hsplit.2 hab hafvBody

lemma not_mem_fvFormula_substFormula_var_of_not_mem_varsFormula {σ : Type}
    (x a b : Var) :
    ∀ φ : Formula σ,
      a ∉ varsFormula (σ := σ) φ →
      b ∉ varsFormula (σ := σ) φ →
      a ≠ b →
      a ∉ fvFormula (σ := σ) (substFormula (σ := σ) x (.var b) φ) := by
  intro φ ha hb hab
  have hEq :
      substFormula (σ := σ) x (.var b) φ =
        substFormulaVarNoAlpha (σ := σ) x b φ :=
    substFormula_var_eq_noAlpha_of_not_mem_varsFormula (σ := σ) x b φ hb
  simpa [hEq] using
    (not_mem_fvFormula_substFormulaVarNoAlpha_of_not_mem_varsFormula
      (σ := σ) x a b φ ha hab)

end Syntax

end Noneism
end HeytingLean
