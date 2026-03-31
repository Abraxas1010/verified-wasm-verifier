import HeytingLean.Noneism.Syntax.Henkin

namespace HeytingLean
namespace Noneism
namespace Syntax
namespace Henkin

/-!
No-alpha substitution helpers for Henkin formulas.

`substFormula` is capture-avoiding, and may rename binders using `freshVar`. In some proof-theory
arguments (Henkin completeness Track J), we only substitute a variable `x` by a *fresh* variable
`a`, so binder-renaming never triggers. This file defines a simple "no-alpha" substitution for that
special case, and proves it agrees with `substFormula` under the standard freshness hypothesis
`a ∉ varsFormula φ`.
-/

variable {σ : Type} {κ : Type u}

/-- Naive (non-capture-avoiding) substitution of variable `x` by variable `a` in a Henkin term. -/
def substTermVarNoAlpha (x a : Var) : TermH κ → TermH κ
  | .var z => if z = x then .var a else .var z
  | .param k => .param k

/-- Naive substitution on lists of terms. -/
def substTermsVarNoAlpha (x a : Var) (ts : List (TermH κ)) : List (TermH κ) :=
  ts.map (substTermVarNoAlpha (κ := κ) x a)

/-- Naive (non-capture-avoiding) substitution of variable `x` by variable `a` in a Henkin formula. -/
def substFormulaVarNoAlpha (x a : Var) : FormulaH σ κ → FormulaH σ κ
  | .top => .top
  | .bot => .bot
  | .pred p args => .pred p (substTermsVarNoAlpha (κ := κ) x a args)
  | .eExists t => .eExists (substTermVarNoAlpha (κ := κ) x a t)
  | .not φ => .not (substFormulaVarNoAlpha x a φ)
  | .and φ ψ => .and (substFormulaVarNoAlpha x a φ) (substFormulaVarNoAlpha x a ψ)
  | .or φ ψ => .or (substFormulaVarNoAlpha x a φ) (substFormulaVarNoAlpha x a ψ)
  | .imp φ ψ => .imp (substFormulaVarNoAlpha x a φ) (substFormulaVarNoAlpha x a ψ)
  | .sigma z φ =>
      if z = x then .sigma z φ else .sigma z (substFormulaVarNoAlpha x a φ)
  | .pi z φ =>
      if z = x then .pi z φ else .pi z (substFormulaVarNoAlpha x a φ)

@[simp] lemma substTermVarNoAlpha_var (x a z : Var) :
    substTermVarNoAlpha (κ := κ) x a (.var z) =
      (if z = x then .var a else .var z) := rfl

@[simp] lemma substTermVarNoAlpha_param (x a : Var) (k : κ) :
    substTermVarNoAlpha (κ := κ) x a (.param k) = .param k := rfl

@[simp] lemma substTermsVarNoAlpha_nil (x a : Var) :
    substTermsVarNoAlpha (κ := κ) x a ([] : List (TermH κ)) = [] := rfl

@[simp] lemma substTermsVarNoAlpha_cons (x a : Var) (t : TermH κ) (ts : List (TermH κ)) :
    substTermsVarNoAlpha (κ := κ) x a (t :: ts) =
      substTermVarNoAlpha (κ := κ) x a t :: substTermsVarNoAlpha (κ := κ) x a ts := by
  simp [substTermsVarNoAlpha]

/--
If `a` is not bound in `φ`, capture-avoiding substitution by `.var a` does not trigger
alpha-renaming and agrees with `substFormulaVarNoAlpha`.
-/
theorem substFormula_var_eq_noAlpha_of_not_mem_boundVars
    (x a : Var) :
    ∀ φ : FormulaH σ κ,
      a ∉ boundVars (σ := σ) (κ := κ) φ →
        substFormula (σ := σ) (κ := κ) x (.var a) φ =
          substFormulaVarNoAlpha (σ := σ) (κ := κ) x a φ := by
  intro φ ha
  induction φ with
  | top =>
      simp [substFormula, substFormulaVarNoAlpha]
  | bot =>
      simp [substFormula, substFormulaVarNoAlpha]
  | pred p args =>
      have hTerm :
          ∀ t : TermH κ,
            substTerm (κ := κ) x (.var a) t = substTermVarNoAlpha (κ := κ) x a t := by
        intro t
        cases t with
        | var z =>
            by_cases hz : z = x <;> simp [substTerm, substTermVarNoAlpha, hz]
        | param k =>
            simp [substTerm, substTermVarNoAlpha]
      have hTerms :
          substTerms (κ := κ) x (.var a) args = substTermsVarNoAlpha (κ := κ) x a args := by
        induction args with
        | nil =>
            simp [substTerms, substTermsVarNoAlpha]
        | cons t ts ih =>
            simp [substTerms, substTermsVarNoAlpha, hTerm]
      simp [substFormula, substFormulaVarNoAlpha, hTerms]
  | eExists t =>
      cases t <;> simp [substFormula, substFormulaVarNoAlpha, substTerm, substTermVarNoAlpha]
  | not φ ih =>
      have ha' : a ∉ boundVars (σ := σ) (κ := κ) φ := by
        simpa [boundVars] using ha
      simpa [substFormula, substFormulaVarNoAlpha] using ih ha'
  | and φ ψ ihφ ihψ =>
      have ha' : a ∉ boundVars (σ := σ) (κ := κ) φ ∧ a ∉ boundVars (σ := σ) (κ := κ) ψ := by
        simpa [boundVars, Finset.mem_union] using ha
      simp [substFormula, substFormulaVarNoAlpha, ihφ ha'.1, ihψ ha'.2]
  | or φ ψ ihφ ihψ =>
      have ha' : a ∉ boundVars (σ := σ) (κ := κ) φ ∧ a ∉ boundVars (σ := σ) (κ := κ) ψ := by
        simpa [boundVars, Finset.mem_union] using ha
      simp [substFormula, substFormulaVarNoAlpha, ihφ ha'.1, ihψ ha'.2]
  | imp φ ψ ihφ ihψ =>
      have ha' : a ∉ boundVars (σ := σ) (κ := κ) φ ∧ a ∉ boundVars (σ := σ) (κ := κ) ψ := by
        simpa [boundVars, Finset.mem_union] using ha
      simp [substFormula, substFormulaVarNoAlpha, ihφ ha'.1, ihψ ha'.2]
  | sigma z φ ih =>
      by_cases hzx : z = x
      · simp [substFormula, substFormulaVarNoAlpha, hzx]
      ·
        have hza : z ≠ a := by
          intro hza
          exact ha (by simp [boundVars, hza, Finset.mem_insert])
        have hbound : a ∉ boundVars (σ := σ) (κ := κ) φ := by
          have : a ≠ z ∧ a ∉ boundVars (σ := σ) (κ := κ) φ := by
            simpa [boundVars] using ha
          exact this.2
        have hcap : ¬(z ∈ fvTerm (κ := κ) (.var a) ∧ x ∈ fvFormula (σ := σ) (κ := κ) φ) := by
          intro h
          have : z = a := by simpa [fvTerm] using h.1
          exact hza this
        simp [substFormula, substFormulaVarNoAlpha, hzx, hcap, ih hbound]
  | pi z φ ih =>
      by_cases hzx : z = x
      · simp [substFormula, substFormulaVarNoAlpha, hzx]
      ·
        have hza : z ≠ a := by
          intro hza
          exact ha (by simp [boundVars, hza, Finset.mem_insert])
        have hbound : a ∉ boundVars (σ := σ) (κ := κ) φ := by
          have : a ≠ z ∧ a ∉ boundVars (σ := σ) (κ := κ) φ := by
            simpa [boundVars] using ha
          exact this.2
        have hcap : ¬(z ∈ fvTerm (κ := κ) (.var a) ∧ x ∈ fvFormula (σ := σ) (κ := κ) φ) := by
          intro h
          have : z = a := by simpa [fvTerm] using h.1
          exact hza this
        simp [substFormula, substFormulaVarNoAlpha, hzx, hcap, ih hbound]

/--
If `a` is fresh for `φ` (in particular, not among its bound variables), then capture-avoiding
substitution by `.var a` does not alpha-rename, and agrees with `substFormulaVarNoAlpha`.
-/
theorem substFormula_var_eq_noAlpha_of_not_mem_varsFormula
    (x a : Var) :
    ∀ φ : FormulaH σ κ,
      a ∉ varsFormula (σ := σ) (κ := κ) φ →
        substFormula (σ := σ) (κ := κ) x (.var a) φ =
          substFormulaVarNoAlpha (σ := σ) (κ := κ) x a φ := by
  intro φ ha
  induction φ with
  | top =>
      simp [substFormula, substFormulaVarNoAlpha]
  | bot =>
      simp [substFormula, substFormulaVarNoAlpha]
  | pred p args =>
      have hTerm :
          ∀ t : TermH κ,
            substTerm (κ := κ) x (.var a) t = substTermVarNoAlpha (κ := κ) x a t := by
        intro t
        cases t with
        | var z =>
            by_cases hz : z = x <;> simp [substTerm, substTermVarNoAlpha, hz]
        | param k =>
            simp [substTerm, substTermVarNoAlpha]
      have hTerms :
          substTerms (κ := κ) x (.var a) args = substTermsVarNoAlpha (κ := κ) x a args := by
        induction args with
        | nil =>
            simp [substTerms, substTermsVarNoAlpha]
        | cons t ts ih =>
            simp [substTerms, substTermsVarNoAlpha, hTerm]
      simp [substFormula, substFormulaVarNoAlpha, hTerms]
  | eExists t =>
      cases t <;> simp [substFormula, substFormulaVarNoAlpha, substTerm, substTermVarNoAlpha]
  | not φ ih =>
      have ha' : a ∉ varsFormula (σ := σ) (κ := κ) φ := by
        simpa [varsFormula] using ha
      simpa [substFormula, substFormulaVarNoAlpha] using ih ha'
  | and φ ψ ihφ ihψ =>
      have ha' : a ∉ varsFormula (σ := σ) (κ := κ) φ ∧ a ∉ varsFormula (σ := σ) (κ := κ) ψ := by
        simpa [varsFormula] using ha
      have haφ : a ∉ varsFormula (σ := σ) (κ := κ) φ := ha'.1
      have haψ : a ∉ varsFormula (σ := σ) (κ := κ) ψ := ha'.2
      simp [substFormula, substFormulaVarNoAlpha, ihφ haφ, ihψ haψ]
  | or φ ψ ihφ ihψ =>
      have ha' : a ∉ varsFormula (σ := σ) (κ := κ) φ ∧ a ∉ varsFormula (σ := σ) (κ := κ) ψ := by
        simpa [varsFormula] using ha
      have haφ : a ∉ varsFormula (σ := σ) (κ := κ) φ := ha'.1
      have haψ : a ∉ varsFormula (σ := σ) (κ := κ) ψ := ha'.2
      simp [substFormula, substFormulaVarNoAlpha, ihφ haφ, ihψ haψ]
  | imp φ ψ ihφ ihψ =>
      have ha' : a ∉ varsFormula (σ := σ) (κ := κ) φ ∧ a ∉ varsFormula (σ := σ) (κ := κ) ψ := by
        simpa [varsFormula] using ha
      have haφ : a ∉ varsFormula (σ := σ) (κ := κ) φ := ha'.1
      have haψ : a ∉ varsFormula (σ := σ) (κ := κ) ψ := ha'.2
      simp [substFormula, substFormulaVarNoAlpha, ihφ haφ, ihψ haψ]
  | sigma z φ ih =>
      by_cases hzx : z = x
      · subst hzx
        simp [substFormula, substFormulaVarNoAlpha]
      ·
        -- Freshness implies `z ≠ a`, hence the capture branch is not taken (since `fvTerm (.var a) = {a}`).
        have hza : z ≠ a := by
          intro hza
          subst hza
          -- `a ∈ varsFormula (.sigma a φ)` by definition.
          exact ha (by simp [varsFormula, Finset.mem_insert])
        have hcap : ¬(z ∈ fvTerm (κ := κ) (.var a) ∧ x ∈ fvFormula (σ := σ) (κ := κ) φ) := by
          intro h
          -- `z ∈ {a}` implies `z = a`, contradiction.
          have : z = a := by simpa [fvTerm] using h.1
          exact hza this
        have ha' : a ∉ varsFormula (σ := σ) (κ := κ) φ := by
          -- `varsFormula (sigma z φ) = insert z (varsFormula φ)`.
          have h : (a ≠ z ∧ a ∉ varsFormula (σ := σ) (κ := κ) φ) := by
            simpa [varsFormula] using ha
          exact h.2
        simp [substFormula, substFormulaVarNoAlpha, hzx, hcap, ih ha']
  | pi z φ ih =>
      by_cases hzx : z = x
      · subst hzx
        simp [substFormula, substFormulaVarNoAlpha]
      ·
        have hza : z ≠ a := by
          intro hza
          subst hza
          exact ha (by simp [varsFormula, Finset.mem_insert])
        have hcap : ¬(z ∈ fvTerm (κ := κ) (.var a) ∧ x ∈ fvFormula (σ := σ) (κ := κ) φ) := by
          intro h
          have : z = a := by simpa [fvTerm] using h.1
          exact hza this
        have ha' : a ∉ varsFormula (σ := σ) (κ := κ) φ := by
          have h : (a ≠ z ∧ a ∉ varsFormula (σ := σ) (κ := κ) φ) := by
            simpa [varsFormula] using ha
          exact h.2
        simp [substFormula, substFormulaVarNoAlpha, hzx, hcap, ih ha']

/--
Substituting a variable by itself never needs alpha-renaming, so the capture-avoiding
substitution agrees with the no-alpha recursion without any freshness hypothesis.
-/
theorem substFormula_var_self_eq_noAlpha
    (x : Var) :
    ∀ φ : FormulaH σ κ,
      substFormula (σ := σ) (κ := κ) x (.var x) φ =
        substFormulaVarNoAlpha (σ := σ) (κ := κ) x x φ := by
  intro φ
  induction φ with
  | top =>
      simp [substFormula, substFormulaVarNoAlpha]
  | bot =>
      simp [substFormula, substFormulaVarNoAlpha]
  | pred p args =>
      have hTerm :
          ∀ t : TermH κ,
            substTerm (κ := κ) x (.var x) t =
              substTermVarNoAlpha (κ := κ) x x t := by
        intro t
        cases t with
        | var z =>
            by_cases hz : z = x <;> simp [substTerm, substTermVarNoAlpha, hz]
        | param k =>
            simp [substTerm, substTermVarNoAlpha]
      have hTerms :
          substTerms (κ := κ) x (.var x) args =
            substTermsVarNoAlpha (κ := κ) x x args := by
        induction args with
        | nil =>
            simp [substTerms, substTermsVarNoAlpha]
        | cons t ts ih =>
            simp [substTerms, substTermsVarNoAlpha, hTerm]
      simp [substFormula, substFormulaVarNoAlpha, hTerms]
  | eExists t =>
      cases t <;> simp [substFormula, substFormulaVarNoAlpha, substTerm, substTermVarNoAlpha]
  | not φ ih =>
      simpa [substFormula, substFormulaVarNoAlpha] using congrArg FormulaH.not ih
  | and φ ψ ihφ ihψ =>
      simp [substFormula, substFormulaVarNoAlpha, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
      simp [substFormula, substFormulaVarNoAlpha, ihφ, ihψ]
  | imp φ ψ ihφ ihψ =>
      simp [substFormula, substFormulaVarNoAlpha, ihφ, ihψ]
  | sigma z φ ih =>
      by_cases hzx : z = x
      · simp [substFormula, substFormulaVarNoAlpha, hzx]
      ·
        have hcap : ¬(z ∈ fvTerm (κ := κ) (.var x) ∧ x ∈ fvFormula (σ := σ) (κ := κ) φ) := by
          intro h
          have : z = x := by simpa [fvTerm] using h.1
          exact hzx this
        simp [substFormula, substFormulaVarNoAlpha, hzx, hcap, ih]
  | pi z φ ih =>
      by_cases hzx : z = x
      · simp [substFormula, substFormulaVarNoAlpha, hzx]
      ·
        have hcap : ¬(z ∈ fvTerm (κ := κ) (.var x) ∧ x ∈ fvFormula (σ := σ) (κ := κ) φ) := by
          intro h
          have : z = x := by simpa [fvTerm] using h.1
          exact hzx this
        simp [substFormula, substFormulaVarNoAlpha, hzx, hcap, ih]

end Henkin
end Syntax
end Noneism
end HeytingLean
