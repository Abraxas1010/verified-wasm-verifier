import HeytingLean.Noneism.Syntax.HenkinNoAlphaSubst

namespace HeytingLean
namespace Noneism
namespace Syntax
namespace Henkin

/-!
Param-to-var rewrite helpers for Henkin formulas.

These lemmas are used in Track A completeness work where a distinguished witness parameter `k`
is rewritten as a variable `a` to align with eigenvariable-style ND rules.
-/

variable {σ : Type} {κ : Type u}

/-- Rewrite a distinguished parameter `k` to variable `a` in a term. -/
def replaceParamWithVarTerm [DecidableEq κ] (k : κ) (a : Var) : TermH κ → TermH κ
  | .var x => .var x
  | .param k' => if k' = k then .var a else .param k'

/-- Rewrite a distinguished parameter `k` to variable `a` in a term-list. -/
def replaceParamWithVarTerms [DecidableEq κ] (k : κ) (a : Var) (ts : List (TermH κ)) :
    List (TermH κ) :=
  ts.map (replaceParamWithVarTerm (κ := κ) k a)

/-- Rewrite a distinguished parameter `k` to variable `a` in a formula. -/
def replaceParamWithVarFormula [DecidableEq κ] (k : κ) (a : Var) : FormulaH σ κ → FormulaH σ κ
  | .top => .top
  | .bot => .bot
  | .pred p args => .pred p (replaceParamWithVarTerms (κ := κ) k a args)
  | .eExists t => .eExists (replaceParamWithVarTerm (κ := κ) k a t)
  | .not φ => .not (replaceParamWithVarFormula k a φ)
  | .and φ ψ => .and (replaceParamWithVarFormula k a φ) (replaceParamWithVarFormula k a ψ)
  | .or φ ψ => .or (replaceParamWithVarFormula k a φ) (replaceParamWithVarFormula k a ψ)
  | .imp φ ψ => .imp (replaceParamWithVarFormula k a φ) (replaceParamWithVarFormula k a ψ)
  | .sigma x φ => .sigma x (replaceParamWithVarFormula k a φ)
  | .pi x φ => .pi x (replaceParamWithVarFormula k a φ)

@[simp] theorem boundVars_replaceParamWithVarFormula [DecidableEq κ]
    (k : κ) (a : Var) (φ : FormulaH σ κ) :
    boundVars (σ := σ) (κ := κ)
      (replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ) =
      boundVars (σ := σ) (κ := κ) φ := by
  induction φ with
  | top =>
      simp [replaceParamWithVarFormula, boundVars]
  | bot =>
      simp [replaceParamWithVarFormula, boundVars]
  | pred p args =>
      simp [replaceParamWithVarFormula, boundVars]
  | eExists t =>
      simp [replaceParamWithVarFormula, boundVars]
  | not φ ih =>
      simp [replaceParamWithVarFormula, boundVars, ih]
  | and φ ψ ihφ ihψ =>
      simp [replaceParamWithVarFormula, boundVars, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
      simp [replaceParamWithVarFormula, boundVars, ihφ, ihψ]
  | imp φ ψ ihφ ihψ =>
      simp [replaceParamWithVarFormula, boundVars, ihφ, ihψ]
  | sigma x φ ih =>
      simp [replaceParamWithVarFormula, boundVars, ih]
  | pi x φ ih =>
      simp [replaceParamWithVarFormula, boundVars, ih]

/-- Naive substitution of variable `x` by parameter `k` (no alpha-renaming branch). -/
def substFormulaParamNoAlpha [DecidableEq κ] (x : Var) (k : κ) : FormulaH σ κ → FormulaH σ κ
  | .top => .top
  | .bot => .bot
  | .pred p args => .pred p (substTerms (κ := κ) x (.param k) args)
  | .eExists t => .eExists (substTerm (κ := κ) x (.param k) t)
  | .not φ => .not (substFormulaParamNoAlpha x k φ)
  | .and φ ψ => .and (substFormulaParamNoAlpha x k φ) (substFormulaParamNoAlpha x k ψ)
  | .or φ ψ => .or (substFormulaParamNoAlpha x k φ) (substFormulaParamNoAlpha x k ψ)
  | .imp φ ψ => .imp (substFormulaParamNoAlpha x k φ) (substFormulaParamNoAlpha x k ψ)
  | .sigma z φ =>
      if z = x then .sigma z φ else .sigma z (substFormulaParamNoAlpha x k φ)
  | .pi z φ =>
      if z = x then .pi z φ else .pi z (substFormulaParamNoAlpha x k φ)

theorem fvTerm_replaceParamWithVarTerm_subset_insert [DecidableEq κ]
    (k : κ) (a : Var) (t : TermH κ) :
    fvTerm (κ := κ) (replaceParamWithVarTerm (κ := κ) k a t) ⊆
      insert a (fvTerm (κ := κ) t) := by
  intro x hx
  cases t with
  | var y =>
      simp [replaceParamWithVarTerm, fvTerm] at hx ⊢
      exact Or.inr hx
  | param k' =>
      by_cases hk : k' = k
      · simp [replaceParamWithVarTerm, fvTerm, hk] at hx ⊢
        exact hx
      · simp [replaceParamWithVarTerm, fvTerm, hk] at hx

theorem fvTerms_replaceParamWithVarTerms_subset_insert [DecidableEq κ]
    (k : κ) (a : Var) (ts : List (TermH κ)) :
    fvTerms (κ := κ) (replaceParamWithVarTerms (κ := κ) k a ts) ⊆
      insert a (fvTerms (κ := κ) ts) := by
  intro x hx
  induction ts with
  | nil =>
      simp [replaceParamWithVarTerms, fvTerms] at hx
  | cons t ts ih =>
      simp [replaceParamWithVarTerms, fvTerms, Finset.mem_union] at hx ⊢
      rcases hx with hx | hx
      ·
        rcases Finset.mem_insert.1
            (fvTerm_replaceParamWithVarTerm_subset_insert (κ := κ) k a t hx) with hEq | hMem
        · exact Or.inl hEq
        · exact Or.inr (Or.inl hMem)
      ·
        rcases Finset.mem_insert.1 (ih hx) with hEq | hMem
        · exact Or.inl hEq
        · exact Or.inr (Or.inr hMem)

theorem varsFormula_replaceParamWithVarFormula_subset_insert [DecidableEq κ]
    (k : κ) (a : Var) (φ : FormulaH σ κ) :
    varsFormula (σ := σ) (κ := κ) (replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ) ⊆
      insert a (varsFormula (σ := σ) (κ := κ) φ) := by
  intro x hx
  induction φ generalizing x with
  | top =>
      simp [replaceParamWithVarFormula, varsFormula] at hx
  | bot =>
      simp [replaceParamWithVarFormula, varsFormula] at hx
  | pred p args =>
      exact fvTerms_replaceParamWithVarTerms_subset_insert (κ := κ) k a args (by
        simpa [replaceParamWithVarFormula, varsFormula] using hx)
  | eExists t =>
      exact fvTerm_replaceParamWithVarTerm_subset_insert (κ := κ) k a t (by
        simpa [replaceParamWithVarFormula, varsFormula] using hx)
  | not φ ih =>
      exact ih (by simpa [replaceParamWithVarFormula, varsFormula] using hx)
  | and φ ψ ihφ ihψ =>
      simp [replaceParamWithVarFormula, varsFormula, Finset.mem_union] at hx ⊢
      rcases hx with hx | hx
      ·
        rcases Finset.mem_insert.1 (ihφ hx) with hEq | hMem
        · exact Or.inl hEq
        · exact Or.inr (Or.inl hMem)
      ·
        rcases Finset.mem_insert.1 (ihψ hx) with hEq | hMem
        · exact Or.inl hEq
        · exact Or.inr (Or.inr hMem)
  | or φ ψ ihφ ihψ =>
      simp [replaceParamWithVarFormula, varsFormula, Finset.mem_union] at hx ⊢
      rcases hx with hx | hx
      ·
        rcases Finset.mem_insert.1 (ihφ hx) with hEq | hMem
        · exact Or.inl hEq
        · exact Or.inr (Or.inl hMem)
      ·
        rcases Finset.mem_insert.1 (ihψ hx) with hEq | hMem
        · exact Or.inl hEq
        · exact Or.inr (Or.inr hMem)
  | imp φ ψ ihφ ihψ =>
      simp [replaceParamWithVarFormula, varsFormula, Finset.mem_union] at hx ⊢
      rcases hx with hx | hx
      ·
        rcases Finset.mem_insert.1 (ihφ hx) with hEq | hMem
        · exact Or.inl hEq
        · exact Or.inr (Or.inl hMem)
      ·
        rcases Finset.mem_insert.1 (ihψ hx) with hEq | hMem
        · exact Or.inl hEq
        · exact Or.inr (Or.inr hMem)
  | sigma z φ ih =>
      simp [replaceParamWithVarFormula, varsFormula, Finset.mem_insert] at hx ⊢
      rcases hx with hEq | hx
      · exact Or.inr (Or.inl hEq)
      ·
        rcases Finset.mem_insert.1 (ih hx) with hEq | hMem
        · exact Or.inl hEq
        · exact Or.inr (Or.inr hMem)
  | pi z φ ih =>
      simp [replaceParamWithVarFormula, varsFormula, Finset.mem_insert] at hx ⊢
      rcases hx with hEq | hx
      · exact Or.inr (Or.inl hEq)
      ·
        rcases Finset.mem_insert.1 (ih hx) with hEq | hMem
        · exact Or.inl hEq
        · exact Or.inr (Or.inr hMem)

theorem fvFormula_replaceParamWithVarFormula_subset_insert [DecidableEq κ]
    (k : κ) (a : Var) (φ : FormulaH σ κ) :
    fvFormula (σ := σ) (κ := κ) (replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ) ⊆
      insert a (fvFormula (σ := σ) (κ := κ) φ) := by
  intro x hx
  induction φ generalizing x with
  | top =>
      simp [replaceParamWithVarFormula, fvFormula] at hx
  | bot =>
      simp [replaceParamWithVarFormula, fvFormula] at hx
  | pred p args =>
      exact fvTerms_replaceParamWithVarTerms_subset_insert (κ := κ) k a args (by
        simpa [replaceParamWithVarFormula, fvFormula] using hx)
  | eExists t =>
      exact fvTerm_replaceParamWithVarTerm_subset_insert (κ := κ) k a t (by
        simpa [replaceParamWithVarFormula, fvFormula] using hx)
  | not φ ih =>
      exact ih (by simpa [replaceParamWithVarFormula, fvFormula] using hx)
  | and φ ψ ihφ ihψ =>
      simp [replaceParamWithVarFormula, fvFormula, Finset.mem_union] at hx ⊢
      rcases hx with hx | hx
      ·
        rcases Finset.mem_insert.1 (ihφ hx) with hEq | hMem
        · exact Or.inl hEq
        · exact Or.inr (Or.inl hMem)
      ·
        rcases Finset.mem_insert.1 (ihψ hx) with hEq | hMem
        · exact Or.inl hEq
        · exact Or.inr (Or.inr hMem)
  | or φ ψ ihφ ihψ =>
      simp [replaceParamWithVarFormula, fvFormula, Finset.mem_union] at hx ⊢
      rcases hx with hx | hx
      ·
        rcases Finset.mem_insert.1 (ihφ hx) with hEq | hMem
        · exact Or.inl hEq
        · exact Or.inr (Or.inl hMem)
      ·
        rcases Finset.mem_insert.1 (ihψ hx) with hEq | hMem
        · exact Or.inl hEq
        · exact Or.inr (Or.inr hMem)
  | imp φ ψ ihφ ihψ =>
      simp [replaceParamWithVarFormula, fvFormula, Finset.mem_union] at hx ⊢
      rcases hx with hx | hx
      ·
        rcases Finset.mem_insert.1 (ihφ hx) with hEq | hMem
        · exact Or.inl hEq
        · exact Or.inr (Or.inl hMem)
      ·
        rcases Finset.mem_insert.1 (ihψ hx) with hEq | hMem
        · exact Or.inl hEq
        · exact Or.inr (Or.inr hMem)
  | sigma z φ ih =>
      have hxNotz : x ≠ z := (Finset.mem_erase.1 hx).1
      have hx' : x ∈ fvFormula (σ := σ) (κ := κ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ) := (Finset.mem_erase.1 hx).2
      have hIn : x ∈ insert a (fvFormula (σ := σ) (κ := κ) φ) := ih hx'
      rcases Finset.mem_insert.1 hIn with hEq | hMem
      · exact Finset.mem_insert.2 (Or.inl hEq)
      · exact Finset.mem_insert.2 (Or.inr (Finset.mem_erase.2 ⟨hxNotz, hMem⟩))
  | pi z φ ih =>
      have hxNotz : x ≠ z := (Finset.mem_erase.1 hx).1
      have hx' : x ∈ fvFormula (σ := σ) (κ := κ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ) := (Finset.mem_erase.1 hx).2
      have hIn : x ∈ insert a (fvFormula (σ := σ) (κ := κ) φ) := ih hx'
      rcases Finset.mem_insert.1 hIn with hEq | hMem
      · exact Finset.mem_insert.2 (Or.inl hEq)
      · exact Finset.mem_insert.2 (Or.inr (Finset.mem_erase.2 ⟨hxNotz, hMem⟩))

theorem not_mem_varsFormula_replaceParamWithVarFormula_of_not_mem_and_ne [DecidableEq κ]
    {a b : Var} {k : κ} {φ : FormulaH σ κ}
    (hb : b ∉ varsFormula (σ := σ) (κ := κ) φ)
    (hba : b ≠ a) :
    b ∉ varsFormula (σ := σ) (κ := κ)
      (replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ) := by
  intro hb'
  have hbIn :
      b ∈ insert a (varsFormula (σ := σ) (κ := κ) φ) :=
    varsFormula_replaceParamWithVarFormula_subset_insert (σ := σ) (κ := κ) k a φ hb'
  rcases Finset.mem_insert.1 hbIn with hEq | hMem
  · exact hba hEq
  · exact hb hMem

theorem not_mem_fvFormula_replaceParamWithVarFormula_of_not_mem_and_ne [DecidableEq κ]
    {a b : Var} {k : κ} {φ : FormulaH σ κ}
    (hb : b ∉ fvFormula (σ := σ) (κ := κ) φ)
    (hba : b ≠ a) :
    b ∉ fvFormula (σ := σ) (κ := κ)
      (replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ) := by
  intro hb'
  have hbIn :
      b ∈ insert a (fvFormula (σ := σ) (κ := κ) φ) :=
    fvFormula_replaceParamWithVarFormula_subset_insert (σ := σ) (κ := κ) k a φ hb'
  rcases Finset.mem_insert.1 hbIn with hEq | hMem
  · exact hba hEq
  · exact hb hMem

/-- Substitution on terms is identity when the substituted variable is not free. -/
theorem substTerm_eq_of_not_mem_fvTerm
    (x : Var) (s : TermH κ) :
    ∀ t : TermH κ, x ∉ fvTerm (κ := κ) t → substTerm (κ := κ) x s t = t := by
  intro t hx
  cases t with
  | var z =>
      by_cases hzx : z = x
      · subst hzx
        exfalso
        exact hx (by simp [fvTerm])
      · simp [substTerm, hzx]
  | param k =>
      simp [substTerm]

/-- Substitution on term-lists is identity when the substituted variable is not free. -/
theorem substTerms_eq_of_not_mem_fvTerms
    (x : Var) (s : TermH κ) :
    ∀ ts : List (TermH κ),
      x ∉ fvTerms (κ := κ) ts →
        substTerms (κ := κ) x s ts = ts := by
  intro ts hx
  induction ts with
  | nil =>
      simp [substTerms]
  | cons t ts ih =>
      have hsplit : x ∉ fvTerm (κ := κ) t ∧ x ∉ fvTerms (κ := κ) ts := by
        simpa [fvTerms_cons, Finset.mem_union] using hx
      have hTail :
          substTerms (κ := κ) x s ts = ts := ih hsplit.2
      have hTailMap :
          List.map (substTerm (κ := κ) x s) ts = ts := by
        simpa [substTerms] using hTail
      simp [substTerms, substTerm_eq_of_not_mem_fvTerm, hsplit.1, hTailMap]

/-- Formula substitution is identity when the substituted variable is not free. -/
theorem substFormula_eq_of_not_mem_fvFormula
    (x : Var) (s : TermH κ) :
    ∀ φ : FormulaH σ κ,
      x ∉ fvFormula (σ := σ) (κ := κ) φ →
        substFormula (σ := σ) (κ := κ) x s φ = φ := by
  intro φ hx
  induction φ with
  | top =>
      simp [substFormula]
  | bot =>
      simp [substFormula]
  | pred p args =>
      have hxArgs : x ∉ fvTerms (κ := κ) args := by
        simpa [fvFormula] using hx
      simp [substFormula, substTerms_eq_of_not_mem_fvTerms, hxArgs]
  | eExists t =>
      have hxT : x ∉ fvTerm (κ := κ) t := by
        simpa [fvFormula] using hx
      simp [substFormula, substTerm_eq_of_not_mem_fvTerm, hxT]
  | not φ ih =>
      have hxφ : x ∉ fvFormula (σ := σ) (κ := κ) φ := by
        simpa [fvFormula] using hx
      simp [substFormula, ih hxφ]
  | and φ ψ ihφ ihψ =>
      have hsplit :
          x ∉ fvFormula (σ := σ) (κ := κ) φ ∧
            x ∉ fvFormula (σ := σ) (κ := κ) ψ := by
        simpa [fvFormula, Finset.mem_union] using hx
      simp [substFormula, ihφ hsplit.1, ihψ hsplit.2]
  | or φ ψ ihφ ihψ =>
      have hsplit :
          x ∉ fvFormula (σ := σ) (κ := κ) φ ∧
            x ∉ fvFormula (σ := σ) (κ := κ) ψ := by
        simpa [fvFormula, Finset.mem_union] using hx
      simp [substFormula, ihφ hsplit.1, ihψ hsplit.2]
  | imp φ ψ ihφ ihψ =>
      have hsplit :
          x ∉ fvFormula (σ := σ) (κ := κ) φ ∧
            x ∉ fvFormula (σ := σ) (κ := κ) ψ := by
        simpa [fvFormula, Finset.mem_union] using hx
      simp [substFormula, ihφ hsplit.1, ihψ hsplit.2]
  | sigma z φ ih =>
      by_cases hzx : z = x
      · subst hzx
        simp [substFormula]
      ·
        have hxz : x ≠ z := by
          intro hzx'
          exact hzx hzx'.symm
        have hxφ : x ∉ fvFormula (σ := σ) (κ := κ) φ := by
          intro hxφ'
          have : x ∈ (fvFormula (σ := σ) (κ := κ) φ).erase z :=
            Finset.mem_erase.2 ⟨hxz, hxφ'⟩
          exact hx (by simpa [fvFormula] using this)
        have hcap :
            ¬(z ∈ fvTerm (κ := κ) s ∧ x ∈ fvFormula (σ := σ) (κ := κ) φ) := by
          intro h
          exact hxφ h.2
        simp [substFormula, hzx, hcap, ih hxφ]
  | pi z φ ih =>
      by_cases hzx : z = x
      · subst hzx
        simp [substFormula]
      ·
        have hxz : x ≠ z := by
          intro hzx'
          exact hzx hzx'.symm
        have hxφ : x ∉ fvFormula (σ := σ) (κ := κ) φ := by
          intro hxφ'
          have : x ∈ (fvFormula (σ := σ) (κ := κ) φ).erase z :=
            Finset.mem_erase.2 ⟨hxz, hxφ'⟩
          exact hx (by simpa [fvFormula] using this)
        have hcap :
            ¬(z ∈ fvTerm (κ := κ) s ∧ x ∈ fvFormula (σ := σ) (κ := κ) φ) := by
          intro h
          exact hxφ h.2
        simp [substFormula, hzx, hcap, ih hxφ]

/--
If distinguished parameter `k` is absent from a term, param→var replacement is identity.
-/
theorem replaceParamWithVarTerm_eq_of_not_mem_paramsTerm [DecidableEq κ]
    (k : κ) (a : Var) (t : TermH κ)
    (hk : k ∉ paramsTerm (κ := κ) t) :
    replaceParamWithVarTerm (κ := κ) k a t = t := by
  cases t with
  | var x =>
      simp [replaceParamWithVarTerm]
  | param k' =>
      have hk' : k' ≠ k := by
        intro hEq
        subst hEq
        exact hk (by simp [paramsTerm])
      simp [replaceParamWithVarTerm, hk']

/--
If distinguished parameter `k` is absent from a term-list, param→var replacement is identity.
-/
theorem replaceParamWithVarTerms_eq_of_not_mem_paramsTerms [DecidableEq κ]
    (k : κ) (a : Var) (ts : List (TermH κ))
    (hk : k ∉ paramsTerms (κ := κ) ts) :
    replaceParamWithVarTerms (κ := κ) k a ts = ts := by
  induction ts with
  | nil =>
      simp [replaceParamWithVarTerms]
  | cons t ts ih =>
      have hkSplit :
          k ∉ paramsTerm (κ := κ) t ∧ k ∉ paramsTerms (κ := κ) ts := by
        simpa [paramsTerms_cons, Finset.mem_union] using hk
      have hTail :
          replaceParamWithVarTerms (κ := κ) k a ts = ts := ih hkSplit.2
      have hTail' :
          List.map (replaceParamWithVarTerm (κ := κ) k a) ts = ts := by
        simpa [replaceParamWithVarTerms] using hTail
      simp [replaceParamWithVarTerms,
        replaceParamWithVarTerm_eq_of_not_mem_paramsTerm, hkSplit.1, hTail']

/--
If distinguished parameter `k` is absent from a formula, param→var replacement is identity.
-/
theorem replaceParamWithVarFormula_eq_of_not_mem_paramsFormula [DecidableEq κ]
    (k : κ) (a : Var) (φ : FormulaH σ κ)
    (hk : k ∉ paramsFormula (σ := σ) (κ := κ) φ) :
    replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ = φ := by
  induction φ with
  | top =>
      simp [replaceParamWithVarFormula]
  | bot =>
      simp [replaceParamWithVarFormula]
  | pred p args =>
      have hkArgs : k ∉ paramsTerms (κ := κ) args := by
        simpa [paramsFormula] using hk
      simpa [replaceParamWithVarFormula] using
        replaceParamWithVarTerms_eq_of_not_mem_paramsTerms (κ := κ) k a args hkArgs
  | eExists t =>
      have hkT : k ∉ paramsTerm (κ := κ) t := by
        simpa [paramsFormula] using hk
      simpa [replaceParamWithVarFormula] using
        replaceParamWithVarTerm_eq_of_not_mem_paramsTerm (κ := κ) k a t hkT
  | not φ ih =>
      have hkφ : k ∉ paramsFormula (σ := σ) (κ := κ) φ := by
        simpa [paramsFormula] using hk
      simp [replaceParamWithVarFormula, ih hkφ]
  | and φ ψ ihφ ihψ =>
      have hkSplit :
          k ∉ paramsFormula (σ := σ) (κ := κ) φ ∧
            k ∉ paramsFormula (σ := σ) (κ := κ) ψ := by
        simpa [paramsFormula, Finset.mem_union] using hk
      simp [replaceParamWithVarFormula, ihφ hkSplit.1, ihψ hkSplit.2]
  | or φ ψ ihφ ihψ =>
      have hkSplit :
          k ∉ paramsFormula (σ := σ) (κ := κ) φ ∧
            k ∉ paramsFormula (σ := σ) (κ := κ) ψ := by
        simpa [paramsFormula, Finset.mem_union] using hk
      simp [replaceParamWithVarFormula, ihφ hkSplit.1, ihψ hkSplit.2]
  | imp φ ψ ihφ ihψ =>
      have hkSplit :
          k ∉ paramsFormula (σ := σ) (κ := κ) φ ∧
            k ∉ paramsFormula (σ := σ) (κ := κ) ψ := by
        simpa [paramsFormula, Finset.mem_union] using hk
      simp [replaceParamWithVarFormula, ihφ hkSplit.1, ihψ hkSplit.2]
  | sigma x φ ih =>
      have hkφ : k ∉ paramsFormula (σ := σ) (κ := κ) φ := by
        simpa [paramsFormula] using hk
      simp [replaceParamWithVarFormula, ih hkφ]
  | pi x φ ih =>
      have hkφ : k ∉ paramsFormula (σ := σ) (κ := κ) φ := by
        simpa [paramsFormula] using hk
      simp [replaceParamWithVarFormula, ih hkφ]

/-- Parameter support is invariant under variable-renaming on terms. -/
theorem paramsTerm_renameTerm
    [DecidableEq κ]
    (x y : Var) (t : TermH κ) :
    paramsTerm (κ := κ) (renameTerm (κ := κ) x y t) =
      paramsTerm (κ := κ) t := by
  cases t with
  | var z =>
      by_cases hz : z = x <;> simp [renameTerm, paramsTerm, hz]
  | param k =>
      simp [renameTerm, paramsTerm]

/-- Parameter support is invariant under variable-renaming on term-lists. -/
theorem paramsTerms_renameTerms
    [DecidableEq κ]
    (x y : Var) (ts : List (TermH κ)) :
    paramsTerms (κ := κ) (renameTerms (κ := κ) x y ts) =
      paramsTerms (κ := κ) ts := by
  induction ts with
  | nil =>
      simp [renameTerms, paramsTerms]
  | cons t ts ih =>
      have ih' : paramsTerms (κ := κ) (List.map (renameTerm (κ := κ) x y) ts) =
          paramsTerms (κ := κ) ts := by
        simpa [renameTerms] using ih
      simp [renameTerms, paramsTerms_cons, paramsTerm_renameTerm, ih']

/-- Parameter support is invariant under variable-renaming on formulas. -/
theorem paramsFormula_renameFormula
    [DecidableEq κ]
    (x y : Var) (φ : FormulaH σ κ) :
    paramsFormula (σ := σ) (κ := κ) (renameFormula (σ := σ) (κ := κ) x y φ) =
      paramsFormula (σ := σ) (κ := κ) φ := by
  induction φ with
  | top =>
      simp [renameFormula, paramsFormula]
  | bot =>
      simp [renameFormula, paramsFormula]
  | pred p args =>
      simp [renameFormula, paramsFormula, paramsTerms_renameTerms]
  | eExists t =>
      simp [renameFormula, paramsFormula, paramsTerm_renameTerm]
  | not φ ih =>
      simpa [renameFormula, paramsFormula] using ih
  | and φ ψ ihφ ihψ =>
      simp [renameFormula, paramsFormula, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
      simp [renameFormula, paramsFormula, ihφ, ihψ]
  | imp φ ψ ihφ ihψ =>
      simp [renameFormula, paramsFormula, ihφ, ihψ]
  | sigma z φ ih =>
      by_cases hz : z = x <;> simp [renameFormula, paramsFormula, hz, ih]
  | pi z φ ih =>
      by_cases hz : z = x <;> simp [renameFormula, paramsFormula, hz, ih]

/-- Substitution by a variable does not change parameter-support on terms. -/
theorem paramsTerm_substTerm_var
    [DecidableEq κ]
    (x b : Var) (t : TermH κ) :
    paramsTerm (κ := κ) (substTerm (κ := κ) x (.var b) t) =
      paramsTerm (κ := κ) t := by
  cases t with
  | var z =>
      by_cases hz : z = x <;> simp [substTerm, paramsTerm, hz]
  | param k =>
      simp [substTerm, paramsTerm]

/-- Substitution by a variable does not change parameter-support on term-lists. -/
theorem paramsTerms_substTerms_var
    [DecidableEq κ]
    (x b : Var) (ts : List (TermH κ)) :
    paramsTerms (κ := κ) (substTerms (κ := κ) x (.var b) ts) =
      paramsTerms (κ := κ) ts := by
  induction ts with
  | nil =>
      simp [substTerms, paramsTerms]
  | cons t ts ih =>
      have ih' : paramsTerms (κ := κ) (List.map (substTerm (κ := κ) x (.var b)) ts) =
          paramsTerms (κ := κ) ts := by
        simpa [substTerms] using ih
      simp [substTerms, paramsTerms_cons, paramsTerm_substTerm_var, ih']

/--
If parameter `k` is absent from `t`, it remains absent after substituting
`x ↦ (.param k')` with `k' ≠ k`.
-/
theorem not_mem_paramsTerm_substTerm_param_of_not_mem_and_ne
    [DecidableEq κ]
    {k k' : κ} {x : Var} {t : TermH κ}
    (hk : k ∉ paramsTerm (κ := κ) t)
    (hk' : k' ≠ k) :
    k ∉ paramsTerm (κ := κ) (substTerm (κ := κ) x (.param k') t) := by
  cases t with
  | var z =>
      by_cases hzx : z = x
      · subst hzx
        simpa [substTerm, paramsTerm, eq_comm] using hk'
      · simp [substTerm, paramsTerm, hzx]
  | param j =>
      have hjk : j ≠ k := by
        intro hjk
        subst hjk
        exact hk (by simp [paramsTerm])
      simpa [substTerm, paramsTerm, eq_comm] using hjk

/--
If parameter `k` is absent from `ts`, it remains absent after substituting
`x ↦ (.param k')` with `k' ≠ k`.
-/
theorem not_mem_paramsTerms_substTerms_param_of_not_mem_and_ne
    [DecidableEq κ]
    {k k' : κ} {x : Var} {ts : List (TermH κ)}
    (hk : k ∉ paramsTerms (κ := κ) ts)
    (hk' : k' ≠ k) :
    k ∉ paramsTerms (κ := κ) (substTerms (κ := κ) x (.param k') ts) := by
  induction ts with
  | nil =>
      simp [substTerms, paramsTerms]
  | cons t ts ih =>
      have hkSplit :
          k ∉ paramsTerm (κ := κ) t ∧ k ∉ paramsTerms (κ := κ) ts := by
        simpa [paramsTerms_cons, Finset.mem_union] using hk
      have hkHead :
          k ∉ paramsTerm (κ := κ) (substTerm (κ := κ) x (.param k') t) :=
        not_mem_paramsTerm_substTerm_param_of_not_mem_and_ne
          (κ := κ) (k := k) (k' := k') (x := x) (t := t) hkSplit.1 hk'
      have hkTail :
          k ∉ paramsTerms (κ := κ) (substTerms (κ := κ) x (.param k') ts) :=
        ih hkSplit.2
      simpa [substTerms, paramsTerms_cons, Finset.mem_union] using And.intro hkHead hkTail

/--
If parameter `k` is absent from `φ`, it remains absent after no-alpha substitution
`x ↦ (.param k')` with `k' ≠ k`.
-/
theorem not_mem_paramsFormula_substFormulaParamNoAlpha_of_not_mem_and_ne
    [DecidableEq κ]
    {k k' : κ} {x : Var} {φ : FormulaH σ κ}
    (hk : k ∉ paramsFormula (σ := σ) (κ := κ) φ)
    (hk' : k' ≠ k) :
    k ∉ paramsFormula (σ := σ) (κ := κ)
      (substFormulaParamNoAlpha (σ := σ) (κ := κ) x k' φ) := by
  induction φ with
  | top =>
      simp [substFormulaParamNoAlpha, paramsFormula] at hk ⊢
  | bot =>
      simp [substFormulaParamNoAlpha, paramsFormula] at hk ⊢
  | pred p args =>
      have hkArgs : k ∉ paramsTerms (κ := κ) args := by
        simpa [paramsFormula] using hk
      have hkSub :
          k ∉ paramsTerms (κ := κ) (substTerms (κ := κ) x (.param k') args) :=
        not_mem_paramsTerms_substTerms_param_of_not_mem_and_ne
          (κ := κ) (k := k) (k' := k') (x := x) (ts := args) hkArgs hk'
      simpa [substFormulaParamNoAlpha, paramsFormula] using hkSub
  | eExists t =>
      have hkT : k ∉ paramsTerm (κ := κ) t := by
        simpa [paramsFormula] using hk
      have hkSub :
          k ∉ paramsTerm (κ := κ) (substTerm (κ := κ) x (.param k') t) :=
        not_mem_paramsTerm_substTerm_param_of_not_mem_and_ne
          (κ := κ) (k := k) (k' := k') (x := x) (t := t) hkT hk'
      simpa [substFormulaParamNoAlpha, paramsFormula] using hkSub
  | not φ ih =>
      have hkφ : k ∉ paramsFormula (σ := σ) (κ := κ) φ := by
        simpa [paramsFormula] using hk
      simpa [substFormulaParamNoAlpha, paramsFormula] using ih hkφ
  | and φ ψ ihφ ihψ =>
      have hkSplit :
          k ∉ paramsFormula (σ := σ) (κ := κ) φ ∧
            k ∉ paramsFormula (σ := σ) (κ := κ) ψ := by
        simpa [paramsFormula, Finset.mem_union] using hk
      have hkL :
          k ∉ paramsFormula (σ := σ) (κ := κ)
            (substFormulaParamNoAlpha (σ := σ) (κ := κ) x k' φ) := ihφ hkSplit.1
      have hkR :
          k ∉ paramsFormula (σ := σ) (κ := κ)
            (substFormulaParamNoAlpha (σ := σ) (κ := κ) x k' ψ) := ihψ hkSplit.2
      simpa [substFormulaParamNoAlpha, paramsFormula, Finset.mem_union] using And.intro hkL hkR
  | or φ ψ ihφ ihψ =>
      have hkSplit :
          k ∉ paramsFormula (σ := σ) (κ := κ) φ ∧
            k ∉ paramsFormula (σ := σ) (κ := κ) ψ := by
        simpa [paramsFormula, Finset.mem_union] using hk
      have hkL :
          k ∉ paramsFormula (σ := σ) (κ := κ)
            (substFormulaParamNoAlpha (σ := σ) (κ := κ) x k' φ) := ihφ hkSplit.1
      have hkR :
          k ∉ paramsFormula (σ := σ) (κ := κ)
            (substFormulaParamNoAlpha (σ := σ) (κ := κ) x k' ψ) := ihψ hkSplit.2
      simpa [substFormulaParamNoAlpha, paramsFormula, Finset.mem_union] using And.intro hkL hkR
  | imp φ ψ ihφ ihψ =>
      have hkSplit :
          k ∉ paramsFormula (σ := σ) (κ := κ) φ ∧
            k ∉ paramsFormula (σ := σ) (κ := κ) ψ := by
        simpa [paramsFormula, Finset.mem_union] using hk
      have hkL :
          k ∉ paramsFormula (σ := σ) (κ := κ)
            (substFormulaParamNoAlpha (σ := σ) (κ := κ) x k' φ) := ihφ hkSplit.1
      have hkR :
          k ∉ paramsFormula (σ := σ) (κ := κ)
            (substFormulaParamNoAlpha (σ := σ) (κ := κ) x k' ψ) := ihψ hkSplit.2
      simpa [substFormulaParamNoAlpha, paramsFormula, Finset.mem_union] using And.intro hkL hkR
  | sigma z φ ih =>
      have hkφ : k ∉ paramsFormula (σ := σ) (κ := κ) φ := by
        simpa [paramsFormula] using hk
      by_cases hzx : z = x
      · simpa [substFormulaParamNoAlpha, paramsFormula, hzx] using hkφ
      ·
        have hkSub :
            k ∉ paramsFormula (σ := σ) (κ := κ)
              (substFormulaParamNoAlpha (σ := σ) (κ := κ) x k' φ) := ih hkφ
        simpa [substFormulaParamNoAlpha, paramsFormula, hzx] using hkSub
  | pi z φ ih =>
      have hkφ : k ∉ paramsFormula (σ := σ) (κ := κ) φ := by
        simpa [paramsFormula] using hk
      by_cases hzx : z = x
      · simpa [substFormulaParamNoAlpha, paramsFormula, hzx] using hkφ
      ·
        have hkSub :
            k ∉ paramsFormula (σ := σ) (κ := κ)
              (substFormulaParamNoAlpha (σ := σ) (κ := κ) x k' φ) := ih hkφ
        simpa [substFormulaParamNoAlpha, paramsFormula, hzx] using hkSub

/--
If parameter `k` is absent from `φ`, it remains absent after substitution `x ↦ (.var b)`.
-/
theorem not_mem_paramsFormula_substFormula_var_of_not_mem
    [DecidableEq κ]
    {k : κ} {x b : Var} {φ : FormulaH σ κ}
    (hk : k ∉ paramsFormula (σ := σ) (κ := κ) φ) :
    k ∉ paramsFormula (σ := σ) (κ := κ)
      (substFormula (σ := σ) (κ := κ) x (.var b) φ) := by
  classical
  have hwf : WellFounded (fun a b' : FormulaH σ κ => fSize a < fSize b') :=
    (InvImage.wf (f := fun ψ : FormulaH σ κ => fSize ψ)
      (r := fun m n : Nat => m < n) Nat.lt_wfRel.wf)
  let C : FormulaH σ κ → Prop :=
    fun ψ =>
      ∀ {k : κ}, k ∉ paramsFormula (σ := σ) (κ := κ) ψ →
        k ∉ paramsFormula (σ := σ) (κ := κ)
          (substFormula (σ := σ) (κ := κ) x (.var b) ψ)
  have hC : ∀ ψ : FormulaH σ κ, C ψ := by
    intro ψ
    refine hwf.induction (C := C) ψ ?_
    intro ψ ih
    intro k hkψ
    cases ψ with
    | top =>
        simp [substFormula, paramsFormula] at hkψ ⊢
    | bot =>
        simp [substFormula, paramsFormula] at hkψ ⊢
    | pred p args =>
        simpa [C, substFormula, paramsFormula, paramsTerms_substTerms_var] using hkψ
    | eExists t =>
        simpa [C, substFormula, paramsFormula, paramsTerm_substTerm_var] using hkψ
    | not ψ =>
        have hkSub :
            k ∉ paramsFormula (σ := σ) (κ := κ)
              (substFormula (σ := σ) (κ := κ) x (.var b) ψ) :=
          ih ψ (by simp [fSize]) (k := k) (by simpa [paramsFormula] using hkψ)
        simpa [C, substFormula, paramsFormula] using hkSub
    | and ψ χ =>
        have hkSplit :
            k ∉ paramsFormula (σ := σ) (κ := κ) ψ ∧
              k ∉ paramsFormula (σ := σ) (κ := κ) χ := by
          simpa [paramsFormula, Finset.mem_union] using hkψ
        have hkSubL :
            k ∉ paramsFormula (σ := σ) (κ := κ)
              (substFormula (σ := σ) (κ := κ) x (.var b) ψ) :=
          ih ψ (by simp [fSize, Nat.add_assoc]) (k := k) hkSplit.1
        have hkSubR :
            k ∉ paramsFormula (σ := σ) (κ := κ)
              (substFormula (σ := σ) (κ := κ) x (.var b) χ) :=
          ih χ (by
            simpa [fSize, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              (Nat.lt_add_of_pos_left (n := fSize χ) (k := fSize ψ + 1) (Nat.succ_pos _)))
            (k := k) hkSplit.2
        simpa [C, substFormula, paramsFormula, Finset.mem_union] using And.intro hkSubL hkSubR
    | or ψ χ =>
        have hkSplit :
            k ∉ paramsFormula (σ := σ) (κ := κ) ψ ∧
              k ∉ paramsFormula (σ := σ) (κ := κ) χ := by
          simpa [paramsFormula, Finset.mem_union] using hkψ
        have hkSubL :
            k ∉ paramsFormula (σ := σ) (κ := κ)
              (substFormula (σ := σ) (κ := κ) x (.var b) ψ) :=
          ih ψ (by simp [fSize, Nat.add_assoc]) (k := k) hkSplit.1
        have hkSubR :
            k ∉ paramsFormula (σ := σ) (κ := κ)
              (substFormula (σ := σ) (κ := κ) x (.var b) χ) :=
          ih χ (by
            simpa [fSize, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              (Nat.lt_add_of_pos_left (n := fSize χ) (k := fSize ψ + 1) (Nat.succ_pos _)))
            (k := k) hkSplit.2
        simpa [C, substFormula, paramsFormula, Finset.mem_union] using And.intro hkSubL hkSubR
    | imp ψ χ =>
        have hkSplit :
            k ∉ paramsFormula (σ := σ) (κ := κ) ψ ∧
              k ∉ paramsFormula (σ := σ) (κ := κ) χ := by
          simpa [paramsFormula, Finset.mem_union] using hkψ
        have hkSubL :
            k ∉ paramsFormula (σ := σ) (κ := κ)
              (substFormula (σ := σ) (κ := κ) x (.var b) ψ) :=
          ih ψ (by simp [fSize, Nat.add_assoc]) (k := k) hkSplit.1
        have hkSubR :
            k ∉ paramsFormula (σ := σ) (κ := κ)
              (substFormula (σ := σ) (κ := κ) x (.var b) χ) :=
          ih χ (by
            simpa [fSize, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              (Nat.lt_add_of_pos_left (n := fSize χ) (k := fSize ψ + 1) (Nat.succ_pos _)))
            (k := k) hkSplit.2
        simpa [C, substFormula, paramsFormula, Finset.mem_union] using And.intro hkSubL hkSubR
    | sigma z ψ =>
        have hkBody : k ∉ paramsFormula (σ := σ) (κ := κ) ψ := by
          simpa [paramsFormula] using hkψ
        by_cases hzx : z = x
        · simpa [C, substFormula, paramsFormula, hzx] using hkBody
        · by_cases hcap : z ∈ fvTerm (κ := κ) (.var b) ∧ x ∈ fvFormula (σ := σ) (κ := κ) ψ
          ·
            let avoid : Finset Var :=
              varsFormula (σ := σ) (κ := κ) ψ ∪ fvTerm (κ := κ) (.var b) ∪ ({x, z} : Finset Var)
            let z' : Var := freshVar avoid
            have hkRen :
                k ∉ paramsFormula (σ := σ) (κ := κ)
                  (renameFormula (σ := σ) (κ := κ) z z' ψ) := by
              simpa [paramsFormula_renameFormula (σ := σ) (κ := κ) z z' ψ] using hkBody
            have hkSub :
                k ∉ paramsFormula (σ := σ) (κ := κ)
                  (substFormula (σ := σ) (κ := κ) x (.var b)
                    (renameFormula (σ := σ) (κ := κ) z z' ψ)) :=
              ih (renameFormula (σ := σ) (κ := κ) z z' ψ)
                (by simp [fSize, fSize_renameFormula]) (k := k) hkRen
            simpa [C, substFormula, paramsFormula, hzx, hcap, avoid, z'] using hkSub
          ·
            have hkSub :
                k ∉ paramsFormula (σ := σ) (κ := κ)
                  (substFormula (σ := σ) (κ := κ) x (.var b) ψ) :=
              ih ψ (by simp [fSize]) (k := k) hkBody
            simpa [C, substFormula, paramsFormula, hzx, hcap] using hkSub
    | pi z ψ =>
        have hkBody : k ∉ paramsFormula (σ := σ) (κ := κ) ψ := by
          simpa [paramsFormula] using hkψ
        by_cases hzx : z = x
        · simpa [C, substFormula, paramsFormula, hzx] using hkBody
        · by_cases hcap : z ∈ fvTerm (κ := κ) (.var b) ∧ x ∈ fvFormula (σ := σ) (κ := κ) ψ
          ·
            let avoid : Finset Var :=
              varsFormula (σ := σ) (κ := κ) ψ ∪ fvTerm (κ := κ) (.var b) ∪ ({x, z} : Finset Var)
            let z' : Var := freshVar avoid
            have hkRen :
                k ∉ paramsFormula (σ := σ) (κ := κ)
                  (renameFormula (σ := σ) (κ := κ) z z' ψ) := by
              simpa [paramsFormula_renameFormula (σ := σ) (κ := κ) z z' ψ] using hkBody
            have hkSub :
                k ∉ paramsFormula (σ := σ) (κ := κ)
                  (substFormula (σ := σ) (κ := κ) x (.var b)
                    (renameFormula (σ := σ) (κ := κ) z z' ψ)) :=
              ih (renameFormula (σ := σ) (κ := κ) z z' ψ)
                (by simp [fSize, fSize_renameFormula]) (k := k) hkRen
            simpa [C, substFormula, paramsFormula, hzx, hcap, avoid, z'] using hkSub
          ·
            have hkSub :
                k ∉ paramsFormula (σ := σ) (κ := κ)
                  (substFormula (σ := σ) (κ := κ) x (.var b) ψ) :=
              ih ψ (by simp [fSize]) (k := k) hkBody
            simpa [C, substFormula, paramsFormula, hzx, hcap] using hkSub
  exact hC φ hk

/--
If parameter `k` is absent from `φ`, then param→var replacement commutes with variable
substitution on `φ` without any extra side conditions.
-/
theorem replaceParamWithVarFormula_substFormula_var_comm_of_not_mem_params
    [DecidableEq κ]
    (k : κ) (a x b : Var) (φ : FormulaH σ κ)
    (hk : k ∉ paramsFormula (σ := σ) (κ := κ) φ) :
    replaceParamWithVarFormula (σ := σ) (κ := κ) k a
        (substFormula (σ := σ) (κ := κ) x (.var b) φ) =
      substFormula (σ := σ) (κ := κ) x (.var b)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ) := by
  have hkSub :
      k ∉ paramsFormula (σ := σ) (κ := κ)
        (substFormula (σ := σ) (κ := κ) x (.var b) φ) :=
    not_mem_paramsFormula_substFormula_var_of_not_mem
      (σ := σ) (κ := κ) (k := k) (x := x) (b := b) (φ := φ) hk
  have hLeft :
      replaceParamWithVarFormula (σ := σ) (κ := κ) k a
        (substFormula (σ := σ) (κ := κ) x (.var b) φ) =
      substFormula (σ := σ) (κ := κ) x (.var b) φ :=
    replaceParamWithVarFormula_eq_of_not_mem_paramsFormula
      (σ := σ) (κ := κ) k a
      (substFormula (σ := σ) (κ := κ) x (.var b) φ) hkSub
  have hRight :
      replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ = φ :=
    replaceParamWithVarFormula_eq_of_not_mem_paramsFormula
      (σ := σ) (κ := κ) k a φ hk
  simp [hLeft, hRight]

theorem substFormula_param_eq_noAlpha [DecidableEq κ]
    (x : Var) (k : κ) :
    ∀ φ : FormulaH σ κ,
      substFormula (σ := σ) (κ := κ) x (.param k) φ =
        substFormulaParamNoAlpha (σ := σ) (κ := κ) x k φ := by
  intro φ
  induction φ with
  | top =>
      simp [substFormula, substFormulaParamNoAlpha]
  | bot =>
      simp [substFormula, substFormulaParamNoAlpha]
  | pred p args =>
      simp [substFormula, substFormulaParamNoAlpha]
  | eExists t =>
      simp [substFormula, substFormulaParamNoAlpha]
  | not φ ih =>
      simpa [substFormula, substFormulaParamNoAlpha] using congrArg FormulaH.not ih
  | and φ ψ ihφ ihψ =>
      simp [substFormula, substFormulaParamNoAlpha, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
      simp [substFormula, substFormulaParamNoAlpha, ihφ, ihψ]
  | imp φ ψ ihφ ihψ =>
      simp [substFormula, substFormulaParamNoAlpha, ihφ, ihψ]
  | sigma z φ ih =>
      by_cases hzx : z = x
      · simp [substFormula, substFormulaParamNoAlpha, hzx]
      ·
        have hcap : ¬(z ∈ fvTerm (κ := κ) (.param k) ∧ x ∈ fvFormula (σ := σ) (κ := κ) φ) := by
          simp [fvTerm]
        simp [substFormula, substFormulaParamNoAlpha, hzx, hcap, ih]
  | pi z φ ih =>
      by_cases hzx : z = x
      · simp [substFormula, substFormulaParamNoAlpha, hzx]
      ·
        have hcap : ¬(z ∈ fvTerm (κ := κ) (.param k) ∧ x ∈ fvFormula (σ := σ) (κ := κ) φ) := by
          simp [fvTerm]
        simp [substFormula, substFormulaParamNoAlpha, hzx, hcap, ih]

/--
If parameter `k` is absent from `φ`, it remains absent after substitution
`x ↦ (.param k')` when `k' ≠ k`.
-/
theorem not_mem_paramsFormula_substFormula_param_of_not_mem_and_ne
    [DecidableEq κ]
    {k k' : κ} {x : Var} {φ : FormulaH σ κ}
    (hk : k ∉ paramsFormula (σ := σ) (κ := κ) φ)
    (hk' : k' ≠ k) :
    k ∉ paramsFormula (σ := σ) (κ := κ)
      (substFormula (σ := σ) (κ := κ) x (.param k') φ) := by
  have hkNoAlpha :
      k ∉ paramsFormula (σ := σ) (κ := κ)
        (substFormulaParamNoAlpha (σ := σ) (κ := κ) x k' φ) :=
    not_mem_paramsFormula_substFormulaParamNoAlpha_of_not_mem_and_ne
      (σ := σ) (κ := κ) (k := k) (k' := k') (x := x) (φ := φ) hk hk'
  simpa [substFormula_param_eq_noAlpha (σ := σ) (κ := κ) x k' φ] using hkNoAlpha

/--
If `k` is absent from `φ`, then param→var replacement commutes with
`x ↦ (.param k')` substitution for any `k' ≠ k`, without variable side-conditions.
-/
theorem replaceParamWithVarFormula_substFormula_param_ne_comm_of_not_mem_params
    [DecidableEq κ]
    (k k' : κ) (a x : Var) (φ : FormulaH σ κ)
    (hk' : k' ≠ k)
    (hk : k ∉ paramsFormula (σ := σ) (κ := κ) φ) :
    replaceParamWithVarFormula (σ := σ) (κ := κ) k a
        (substFormula (σ := σ) (κ := κ) x (.param k') φ) =
      substFormula (σ := σ) (κ := κ) x (.param k')
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ) := by
  have hkSub :
      k ∉ paramsFormula (σ := σ) (κ := κ)
        (substFormula (σ := σ) (κ := κ) x (.param k') φ) :=
    not_mem_paramsFormula_substFormula_param_of_not_mem_and_ne
      (σ := σ) (κ := κ) (k := k) (k' := k') (x := x) (φ := φ) hk hk'
  have hLeft :
      replaceParamWithVarFormula (σ := σ) (κ := κ) k a
        (substFormula (σ := σ) (κ := κ) x (.param k') φ) =
      substFormula (σ := σ) (κ := κ) x (.param k') φ :=
    replaceParamWithVarFormula_eq_of_not_mem_paramsFormula
      (σ := σ) (κ := κ) k a
      (substFormula (σ := σ) (κ := κ) x (.param k') φ) hkSub
  have hRight :
      replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ = φ :=
    replaceParamWithVarFormula_eq_of_not_mem_paramsFormula
      (σ := σ) (κ := κ) k a φ hk
  simp [hLeft, hRight]

theorem fvTerm_substTermVarNoAlpha_subset_insert
    [DecidableEq κ]
    (x b : Var) (t : TermH κ) :
    fvTerm (κ := κ) (substTermVarNoAlpha (κ := κ) x b t) ⊆
      insert b (fvTerm (κ := κ) t) := by
  intro a ha
  cases t with
  | var y =>
      by_cases hy : y = x
      · subst hy
        simp [substTermVarNoAlpha, fvTerm] at ha ⊢
        exact Or.inl ha
      · simp [substTermVarNoAlpha, fvTerm, hy] at ha ⊢
        exact Or.inr ha
  | param k =>
      simp [substTermVarNoAlpha, fvTerm] at ha

theorem fvTerms_substTermsVarNoAlpha_subset_insert
    [DecidableEq κ]
    (x b : Var) (ts : List (TermH κ)) :
    fvTerms (κ := κ) (substTermsVarNoAlpha (κ := κ) x b ts) ⊆
      insert b (fvTerms (κ := κ) ts) := by
  intro a ha
  induction ts with
  | nil =>
      simp [substTermsVarNoAlpha, fvTerms] at ha
  | cons t ts ih =>
      simp [substTermsVarNoAlpha, fvTerms_cons, Finset.mem_union] at ha ⊢
      rcases ha with ha | ha
      ·
        rcases Finset.mem_insert.1 (fvTerm_substTermVarNoAlpha_subset_insert
          (κ := κ) x b t ha) with hEq | hMem
        · exact Or.inl hEq
        · exact Or.inr (Or.inl hMem)
      ·
        rcases Finset.mem_insert.1 (ih ha) with hEq | hMem
        · exact Or.inl hEq
        · exact Or.inr (Or.inr hMem)

theorem fvTerm_substTermParam_subset
    [DecidableEq κ]
    (x : Var) (k : κ) (t : TermH κ) :
    fvTerm (κ := κ) (substTerm (κ := κ) x (.param k) t) ⊆
      fvTerm (κ := κ) t := by
  intro a ha
  cases t with
  | var y =>
      by_cases hy : y = x
      · subst hy
        simp [substTerm, fvTerm] at ha
      ·
        simp [substTerm, fvTerm, hy] at ha ⊢
        exact ha
  | param k' =>
      simp [substTerm, fvTerm] at ha

theorem fvTerms_substTermsParam_subset
    [DecidableEq κ]
    (x : Var) (k : κ) (ts : List (TermH κ)) :
    fvTerms (κ := κ) (substTerms (κ := κ) x (.param k) ts) ⊆
      fvTerms (κ := κ) ts := by
  intro a ha
  induction ts with
  | nil =>
      simp [substTerms, fvTerms] at ha
  | cons t ts ih =>
      simp [substTerms, fvTerms_cons, Finset.mem_union] at ha ⊢
      rcases ha with ha | ha
      · exact Or.inl (fvTerm_substTermParam_subset (κ := κ) x k t ha)
      · exact Or.inr (ih ha)

theorem varsFormula_substFormulaVarNoAlpha_subset_insert
    [DecidableEq κ]
    (x b : Var) (φ : FormulaH σ κ) :
    varsFormula (σ := σ) (κ := κ)
      (substFormulaVarNoAlpha (σ := σ) (κ := κ) x b φ) ⊆
      insert b (varsFormula (σ := σ) (κ := κ) φ) := by
  intro a ha
  induction φ generalizing a with
  | top =>
      simp [substFormulaVarNoAlpha, varsFormula] at ha
  | bot =>
      simp [substFormulaVarNoAlpha, varsFormula] at ha
  | pred p args =>
      exact fvTerms_substTermsVarNoAlpha_subset_insert (κ := κ) x b args (by
        simpa [substFormulaVarNoAlpha, varsFormula] using ha)
  | eExists t =>
      exact fvTerm_substTermVarNoAlpha_subset_insert (κ := κ) x b t (by
        simpa [substFormulaVarNoAlpha, varsFormula] using ha)
  | not φ ih =>
      exact ih (by simpa [substFormulaVarNoAlpha, varsFormula] using ha)
  | and φ ψ ihφ ihψ =>
      simp [substFormulaVarNoAlpha, varsFormula, Finset.mem_union] at ha ⊢
      rcases ha with ha | ha
      ·
        rcases Finset.mem_insert.1 (ihφ ha) with hEq | hMem
        · exact Or.inl hEq
        · exact Or.inr (Or.inl hMem)
      ·
        rcases Finset.mem_insert.1 (ihψ ha) with hEq | hMem
        · exact Or.inl hEq
        · exact Or.inr (Or.inr hMem)
  | or φ ψ ihφ ihψ =>
      simp [substFormulaVarNoAlpha, varsFormula, Finset.mem_union] at ha ⊢
      rcases ha with ha | ha
      ·
        rcases Finset.mem_insert.1 (ihφ ha) with hEq | hMem
        · exact Or.inl hEq
        · exact Or.inr (Or.inl hMem)
      ·
        rcases Finset.mem_insert.1 (ihψ ha) with hEq | hMem
        · exact Or.inl hEq
        · exact Or.inr (Or.inr hMem)
  | imp φ ψ ihφ ihψ =>
      simp [substFormulaVarNoAlpha, varsFormula, Finset.mem_union] at ha ⊢
      rcases ha with ha | ha
      ·
        rcases Finset.mem_insert.1 (ihφ ha) with hEq | hMem
        · exact Or.inl hEq
        · exact Or.inr (Or.inl hMem)
      ·
        rcases Finset.mem_insert.1 (ihψ ha) with hEq | hMem
        · exact Or.inl hEq
        · exact Or.inr (Or.inr hMem)
  | sigma z φ ih =>
      by_cases hzx : z = x
      ·
        simp [substFormulaVarNoAlpha, varsFormula, hzx, Finset.mem_insert] at ha ⊢
        rcases ha with hEq | hMem
        · exact Or.inr (Or.inl hEq)
        · exact Or.inr (Or.inr hMem)
      ·
        simp [substFormulaVarNoAlpha, varsFormula, hzx, Finset.mem_insert] at ha ⊢
        rcases ha with hEq | ha
        · exact Or.inr (Or.inl hEq)
        ·
          rcases Finset.mem_insert.1 (ih ha) with hEq | hMem
          · exact Or.inl hEq
          · exact Or.inr (Or.inr hMem)
  | pi z φ ih =>
      by_cases hzx : z = x
      ·
        simp [substFormulaVarNoAlpha, varsFormula, hzx, Finset.mem_insert] at ha ⊢
        rcases ha with hEq | hMem
        · exact Or.inr (Or.inl hEq)
        · exact Or.inr (Or.inr hMem)
      ·
        simp [substFormulaVarNoAlpha, varsFormula, hzx, Finset.mem_insert] at ha ⊢
        rcases ha with hEq | ha
        · exact Or.inr (Or.inl hEq)
        ·
          rcases Finset.mem_insert.1 (ih ha) with hEq | hMem
          · exact Or.inl hEq
          · exact Or.inr (Or.inr hMem)

theorem not_mem_varsFormula_substFormulaVarNoAlpha_of_not_mem_and_ne
    [DecidableEq κ]
    {a b x : Var} {φ : FormulaH σ κ}
    (ha : a ∉ varsFormula (σ := σ) (κ := κ) φ)
    (hab : a ≠ b) :
    a ∉ varsFormula (σ := σ) (κ := κ)
      (substFormulaVarNoAlpha (σ := σ) (κ := κ) x b φ) := by
  intro ha'
  have hIn :
      a ∈ insert b (varsFormula (σ := σ) (κ := κ) φ) :=
    varsFormula_substFormulaVarNoAlpha_subset_insert (σ := σ) (κ := κ) x b φ ha'
  rcases Finset.mem_insert.1 hIn with hEq | hMem
  · exact hab hEq
  · exact ha hMem

theorem varsFormula_substFormulaParamNoAlpha_subset
    [DecidableEq κ]
    (x : Var) (k : κ) (φ : FormulaH σ κ) :
    varsFormula (σ := σ) (κ := κ)
      (substFormulaParamNoAlpha (σ := σ) (κ := κ) x k φ) ⊆
      varsFormula (σ := σ) (κ := κ) φ := by
  intro a ha
  induction φ generalizing a with
  | top =>
      simp [substFormulaParamNoAlpha, varsFormula] at ha
  | bot =>
      simp [substFormulaParamNoAlpha, varsFormula] at ha
  | pred p args =>
      exact fvTerms_substTermsParam_subset (κ := κ) x k args (by
        simpa [substFormulaParamNoAlpha, varsFormula] using ha)
  | eExists t =>
      exact fvTerm_substTermParam_subset (κ := κ) x k t (by
        simpa [substFormulaParamNoAlpha, varsFormula] using ha)
  | not φ ih =>
      exact ih (by simpa [substFormulaParamNoAlpha, varsFormula] using ha)
  | and φ ψ ihφ ihψ =>
      simp [substFormulaParamNoAlpha, varsFormula, Finset.mem_union] at ha ⊢
      rcases ha with ha | ha
      · exact Or.inl (ihφ ha)
      · exact Or.inr (ihψ ha)
  | or φ ψ ihφ ihψ =>
      simp [substFormulaParamNoAlpha, varsFormula, Finset.mem_union] at ha ⊢
      rcases ha with ha | ha
      · exact Or.inl (ihφ ha)
      · exact Or.inr (ihψ ha)
  | imp φ ψ ihφ ihψ =>
      simp [substFormulaParamNoAlpha, varsFormula, Finset.mem_union] at ha ⊢
      rcases ha with ha | ha
      · exact Or.inl (ihφ ha)
      · exact Or.inr (ihψ ha)
  | sigma z φ ih =>
      by_cases hzx : z = x
      ·
        simp [substFormulaParamNoAlpha, varsFormula, hzx, Finset.mem_insert] at ha ⊢
        exact ha
      ·
        simp [substFormulaParamNoAlpha, varsFormula, hzx, Finset.mem_insert] at ha ⊢
        rcases ha with hEq | ha'
        · exact Or.inl hEq
        · exact Or.inr (ih ha')
  | pi z φ ih =>
      by_cases hzx : z = x
      ·
        simp [substFormulaParamNoAlpha, varsFormula, hzx, Finset.mem_insert] at ha ⊢
        exact ha
      ·
        simp [substFormulaParamNoAlpha, varsFormula, hzx, Finset.mem_insert] at ha ⊢
        rcases ha with hEq | ha'
        · exact Or.inl hEq
        · exact Or.inr (ih ha')

theorem not_mem_varsFormula_substFormula_param_of_not_mem
    [DecidableEq κ]
    {a x : Var} {k : κ} {φ : FormulaH σ κ}
    (ha : a ∉ varsFormula (σ := σ) (κ := κ) φ) :
    a ∉ varsFormula (σ := σ) (κ := κ)
      (substFormula (σ := σ) (κ := κ) x (.param k) φ) := by
  intro ha'
  have hIn :
      a ∈ varsFormula (σ := σ) (κ := κ)
        (substFormulaParamNoAlpha (σ := σ) (κ := κ) x k φ) := by
    simpa [substFormula_param_eq_noAlpha (σ := σ) (κ := κ) x k φ] using ha'
  exact ha (varsFormula_substFormulaParamNoAlpha_subset
    (σ := σ) (κ := κ) x k φ hIn)

theorem not_mem_varsFormula_substFormula_var_of_not_mem_and_ne
    [DecidableEq κ]
    {a b x : Var} {φ : FormulaH σ κ}
    (ha : a ∉ varsFormula (σ := σ) (κ := κ) φ)
    (hab : a ≠ b)
    (hb : b ∉ varsFormula (σ := σ) (κ := κ) φ) :
    a ∉ varsFormula (σ := σ) (κ := κ)
      (substFormula (σ := σ) (κ := κ) x (.var b) φ) := by
  have hEq :
      substFormula (σ := σ) (κ := κ) x (.var b) φ =
        substFormulaVarNoAlpha (σ := σ) (κ := κ) x b φ := by
    exact substFormula_var_eq_noAlpha_of_not_mem_varsFormula
      (σ := σ) (κ := κ) x b φ hb
  intro ha'
  exact not_mem_varsFormula_substFormulaVarNoAlpha_of_not_mem_and_ne
    (σ := σ) (κ := κ) (a := a) (b := b) (x := x) (φ := φ) ha hab (by
      simpa [hEq] using ha')

theorem replaceParamWithVarTerm_substTermVarNoAlpha_comm [DecidableEq κ]
    (k : κ) (a x b : Var) (hxa : x ≠ a) (t : TermH κ) :
    replaceParamWithVarTerm (κ := κ) k a (substTermVarNoAlpha (κ := κ) x b t) =
      substTermVarNoAlpha (κ := κ) x b (replaceParamWithVarTerm (κ := κ) k a t) := by
  cases t with
  | var y =>
      by_cases hy : y = x <;> simp [substTermVarNoAlpha, replaceParamWithVarTerm, hy]
  | param k' =>
      by_cases hk : k' = k
      · have hax : a ≠ x := Ne.symm hxa
        simp [substTermVarNoAlpha, replaceParamWithVarTerm, hk, hax]
      · simp [substTermVarNoAlpha, replaceParamWithVarTerm, hk]

theorem replaceParamWithVarTerm_substTermParam_comm [DecidableEq κ]
    (k : κ) (a x : Var) (t : TermH κ) :
    replaceParamWithVarTerm (κ := κ) k a (substTerm (κ := κ) x (.param k) t) =
      substTermVarNoAlpha (κ := κ) x a (replaceParamWithVarTerm (κ := κ) k a t) := by
  cases t with
  | var y =>
      by_cases hy : y = x <;> simp [substTerm, substTermVarNoAlpha, replaceParamWithVarTerm, hy]
  | param k' =>
      by_cases hk : k' = k <;> simp [substTerm, substTermVarNoAlpha, replaceParamWithVarTerm, hk]

theorem replaceParamWithVarTerm_substTermParam_ne_comm [DecidableEq κ]
    (k k' : κ) (a x : Var) (hk' : k' ≠ k) (hxa : x ≠ a) (t : TermH κ) :
    replaceParamWithVarTerm (κ := κ) k a (substTerm (κ := κ) x (.param k') t) =
      substTerm (κ := κ) x (.param k') (replaceParamWithVarTerm (κ := κ) k a t) := by
  cases t with
  | var y =>
      by_cases hy : y = x <;> simp [substTerm, replaceParamWithVarTerm, hy, hk']
  | param k0 =>
      by_cases hk0 : k0 = k
      · subst hk0
        have hax : a ≠ x := Ne.symm hxa
        simp [substTerm, replaceParamWithVarTerm, hax]
      · simp [substTerm, replaceParamWithVarTerm, hk0]

theorem replaceParamWithVarTerms_substTermsParam_comm [DecidableEq κ]
    (k : κ) (a x : Var) (ts : List (TermH κ)) :
    replaceParamWithVarTerms (κ := κ) k a (substTerms (κ := κ) x (.param k) ts) =
      substTermsVarNoAlpha (κ := κ) x a (replaceParamWithVarTerms (κ := κ) k a ts) := by
  induction ts with
  | nil =>
      simp [replaceParamWithVarTerms, substTerms, substTermsVarNoAlpha]
  | cons t ts ih =>
      simp [replaceParamWithVarTerms, substTerms, substTermsVarNoAlpha,
        replaceParamWithVarTerm_substTermParam_comm]

theorem replaceParamWithVarTerms_substTermsParam_ne_comm [DecidableEq κ]
    (k k' : κ) (a x : Var) (hk' : k' ≠ k) (hxa : x ≠ a) (ts : List (TermH κ)) :
    replaceParamWithVarTerms (κ := κ) k a (substTerms (κ := κ) x (.param k') ts) =
      substTerms (κ := κ) x (.param k') (replaceParamWithVarTerms (κ := κ) k a ts) := by
  induction ts with
  | nil =>
      simp [replaceParamWithVarTerms, substTerms]
  | cons t ts ih =>
      simp [replaceParamWithVarTerms, substTerms,
        replaceParamWithVarTerm_substTermParam_ne_comm, hk', hxa]

theorem replaceParamWithVarTerms_substTermsVarNoAlpha_comm [DecidableEq κ]
    (k : κ) (a x b : Var) (hxa : x ≠ a) (ts : List (TermH κ)) :
    replaceParamWithVarTerms (κ := κ) k a (substTermsVarNoAlpha (κ := κ) x b ts) =
      substTermsVarNoAlpha (κ := κ) x b (replaceParamWithVarTerms (κ := κ) k a ts) := by
  induction ts with
  | nil =>
      simp [replaceParamWithVarTerms, substTermsVarNoAlpha]
  | cons t ts ih =>
      simp [replaceParamWithVarTerms, substTermsVarNoAlpha,
        replaceParamWithVarTerm_substTermVarNoAlpha_comm, hxa]

theorem replaceParamWithVarFormula_substFormulaVarNoAlpha_comm [DecidableEq κ]
    (k : κ) (a x b : Var) (hxa : x ≠ a) (φ : FormulaH σ κ) :
    replaceParamWithVarFormula (σ := σ) (κ := κ) k a
        (substFormulaVarNoAlpha (σ := σ) (κ := κ) x b φ) =
      substFormulaVarNoAlpha (σ := σ) (κ := κ) x b
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ) := by
  induction φ with
  | top =>
      simp [replaceParamWithVarFormula, substFormulaVarNoAlpha]
  | bot =>
      simp [replaceParamWithVarFormula, substFormulaVarNoAlpha]
  | pred p args =>
      simp [replaceParamWithVarFormula, substFormulaVarNoAlpha,
        replaceParamWithVarTerms_substTermsVarNoAlpha_comm, hxa]
  | eExists t =>
      simp [replaceParamWithVarFormula, substFormulaVarNoAlpha,
        replaceParamWithVarTerm_substTermVarNoAlpha_comm, hxa]
  | not φ ih =>
      simpa [replaceParamWithVarFormula, substFormulaVarNoAlpha] using congrArg FormulaH.not ih
  | and φ ψ ihφ ihψ =>
      simp [replaceParamWithVarFormula, substFormulaVarNoAlpha, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
      simp [replaceParamWithVarFormula, substFormulaVarNoAlpha, ihφ, ihψ]
  | imp φ ψ ihφ ihψ =>
      simp [replaceParamWithVarFormula, substFormulaVarNoAlpha, ihφ, ihψ]
  | sigma z φ ih =>
      by_cases hzx : z = x <;> simp [replaceParamWithVarFormula, substFormulaVarNoAlpha, hzx, ih]
  | pi z φ ih =>
      by_cases hzx : z = x <;> simp [replaceParamWithVarFormula, substFormulaVarNoAlpha, hzx, ih]

theorem replaceParamWithVarFormula_substFormulaParamNoAlpha_comm [DecidableEq κ]
    (k : κ) (a x : Var) (φ : FormulaH σ κ) :
    replaceParamWithVarFormula (σ := σ) (κ := κ) k a
        (substFormulaParamNoAlpha (σ := σ) (κ := κ) x k φ) =
      substFormulaVarNoAlpha (σ := σ) (κ := κ) x a
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ) := by
  induction φ with
  | top =>
      simp [replaceParamWithVarFormula, substFormulaParamNoAlpha, substFormulaVarNoAlpha]
  | bot =>
      simp [replaceParamWithVarFormula, substFormulaParamNoAlpha, substFormulaVarNoAlpha]
  | pred p args =>
      simp [replaceParamWithVarFormula, substFormulaParamNoAlpha, substFormulaVarNoAlpha,
        replaceParamWithVarTerms_substTermsParam_comm]
  | eExists t =>
      simp [replaceParamWithVarFormula, substFormulaParamNoAlpha, substFormulaVarNoAlpha,
        replaceParamWithVarTerm_substTermParam_comm]
  | not φ ih =>
      simpa [replaceParamWithVarFormula, substFormulaParamNoAlpha, substFormulaVarNoAlpha] using
        congrArg FormulaH.not ih
  | and φ ψ ihφ ihψ =>
      simp [replaceParamWithVarFormula, substFormulaParamNoAlpha, substFormulaVarNoAlpha, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
      simp [replaceParamWithVarFormula, substFormulaParamNoAlpha, substFormulaVarNoAlpha, ihφ, ihψ]
  | imp φ ψ ihφ ihψ =>
      simp [replaceParamWithVarFormula, substFormulaParamNoAlpha, substFormulaVarNoAlpha, ihφ, ihψ]
  | sigma z φ ih =>
      by_cases hzx : z = x <;>
        simp [replaceParamWithVarFormula, substFormulaParamNoAlpha, substFormulaVarNoAlpha, hzx, ih]
  | pi z φ ih =>
      by_cases hzx : z = x <;>
        simp [replaceParamWithVarFormula, substFormulaParamNoAlpha, substFormulaVarNoAlpha, hzx, ih]

theorem replaceParamWithVarFormula_substFormulaParamNoAlpha_ne_comm [DecidableEq κ]
    (k k' : κ) (a x : Var) (hk' : k' ≠ k) (hxa : x ≠ a) (φ : FormulaH σ κ) :
    replaceParamWithVarFormula (σ := σ) (κ := κ) k a
        (substFormulaParamNoAlpha (σ := σ) (κ := κ) x k' φ) =
      substFormulaParamNoAlpha (σ := σ) (κ := κ) x k'
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ) := by
  induction φ with
  | top =>
      simp [replaceParamWithVarFormula, substFormulaParamNoAlpha]
  | bot =>
      simp [replaceParamWithVarFormula, substFormulaParamNoAlpha]
  | pred p args =>
      simp [replaceParamWithVarFormula, substFormulaParamNoAlpha,
        replaceParamWithVarTerms_substTermsParam_ne_comm, hk', hxa]
  | eExists t =>
      simp [replaceParamWithVarFormula, substFormulaParamNoAlpha,
        replaceParamWithVarTerm_substTermParam_ne_comm, hk', hxa]
  | not φ ih =>
      simpa [replaceParamWithVarFormula, substFormulaParamNoAlpha] using congrArg FormulaH.not ih
  | and φ ψ ihφ ihψ =>
      simp [replaceParamWithVarFormula, substFormulaParamNoAlpha, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
      simp [replaceParamWithVarFormula, substFormulaParamNoAlpha, ihφ, ihψ]
  | imp φ ψ ihφ ihψ =>
      simp [replaceParamWithVarFormula, substFormulaParamNoAlpha, ihφ, ihψ]
  | sigma z φ ih =>
      by_cases hzx : z = x <;>
        simp [replaceParamWithVarFormula, substFormulaParamNoAlpha, hzx, ih]
  | pi z φ ih =>
      by_cases hzx : z = x <;>
        simp [replaceParamWithVarFormula, substFormulaParamNoAlpha, hzx, ih]

theorem replaceParamWithVarFormula_substFormula_param_ne_comm [DecidableEq κ]
    (k k' : κ) (a x : Var) (hk' : k' ≠ k) (hxa : x ≠ a) (φ : FormulaH σ κ) :
    replaceParamWithVarFormula (σ := σ) (κ := κ) k a
        (substFormula (σ := σ) (κ := κ) x (.param k') φ) =
      substFormula (σ := σ) (κ := κ) x (.param k')
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ) := by
  calc
    replaceParamWithVarFormula (σ := σ) (κ := κ) k a
        (substFormula (σ := σ) (κ := κ) x (.param k') φ)
        =
      replaceParamWithVarFormula (σ := σ) (κ := κ) k a
        (substFormulaParamNoAlpha (σ := σ) (κ := κ) x k' φ) := by
          simp [substFormula_param_eq_noAlpha (σ := σ) (κ := κ) x k' φ]
    _ =
      substFormulaParamNoAlpha (σ := σ) (κ := κ) x k'
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ) := by
          simpa using replaceParamWithVarFormula_substFormulaParamNoAlpha_ne_comm
            (σ := σ) (κ := κ) k k' a x hk' hxa φ
    _ =
      substFormula (σ := σ) (κ := κ) x (.param k')
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ) := by
          symm
          simp [substFormula_param_eq_noAlpha (σ := σ) (κ := κ) x k'
            (replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ)]

theorem replaceParamWithVarFormula_substFormula_param_comm_of_not_mem [DecidableEq κ]
    (k : κ) (a x : Var) (φ : FormulaH σ κ)
    (ha :
      a ∉ varsFormula (σ := σ) (κ := κ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ)) :
    replaceParamWithVarFormula (σ := σ) (κ := κ) k a
        (substFormula (σ := σ) (κ := κ) x (.param k) φ) =
      substFormula (σ := σ) (κ := κ) x (.var a)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ) := by
  calc
    replaceParamWithVarFormula (σ := σ) (κ := κ) k a
        (substFormula (σ := σ) (κ := κ) x (.param k) φ)
        =
      replaceParamWithVarFormula (σ := σ) (κ := κ) k a
        (substFormulaParamNoAlpha (σ := σ) (κ := κ) x k φ) := by
          simp [substFormula_param_eq_noAlpha (σ := σ) (κ := κ) x k φ]
    _ =
      substFormulaVarNoAlpha (σ := σ) (κ := κ) x a
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ) := by
          simpa using replaceParamWithVarFormula_substFormulaParamNoAlpha_comm
            (σ := σ) (κ := κ) k a x φ
    _ =
      substFormula (σ := σ) (κ := κ) x (.var a)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ) := by
          symm
          simp [substFormula_var_eq_noAlpha_of_not_mem_varsFormula (σ := σ) (κ := κ) x a
            (replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ) ha]

theorem replaceParamWithVarFormula_substFormula_param_comm_of_not_mem_boundVars [DecidableEq κ]
    (k : κ) (a x : Var) (φ : FormulaH σ κ)
    (ha :
      a ∉ boundVars (σ := σ) (κ := κ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ)) :
    replaceParamWithVarFormula (σ := σ) (κ := κ) k a
        (substFormula (σ := σ) (κ := κ) x (.param k) φ) =
      substFormula (σ := σ) (κ := κ) x (.var a)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ) := by
  calc
    replaceParamWithVarFormula (σ := σ) (κ := κ) k a
        (substFormula (σ := σ) (κ := κ) x (.param k) φ)
        =
      replaceParamWithVarFormula (σ := σ) (κ := κ) k a
        (substFormulaParamNoAlpha (σ := σ) (κ := κ) x k φ) := by
          simp [substFormula_param_eq_noAlpha (σ := σ) (κ := κ) x k φ]
    _ =
      substFormulaVarNoAlpha (σ := σ) (κ := κ) x a
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ) := by
          simpa using replaceParamWithVarFormula_substFormulaParamNoAlpha_comm
            (σ := σ) (κ := κ) k a x φ
    _ =
      substFormula (σ := σ) (κ := κ) x (.var a)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ) := by
          symm
          simp [substFormula_var_eq_noAlpha_of_not_mem_boundVars (σ := σ) (κ := κ) x a
            (replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ) ha]

theorem replaceParamWithVarFormula_substFormula_var_comm_of_not_mem_and_ne [DecidableEq κ]
    (k : κ) (a x b : Var) (φ : FormulaH σ κ)
    (hb : b ∉ varsFormula (σ := σ) (κ := κ) φ)
    (hba : b ≠ a)
    (hxa : x ≠ a) :
    replaceParamWithVarFormula (σ := σ) (κ := κ) k a
        (substFormula (σ := σ) (κ := κ) x (.var b) φ) =
      substFormula (σ := σ) (κ := κ) x (.var b)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ) := by
  have hb' :
      b ∉ varsFormula (σ := σ) (κ := κ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ) :=
    not_mem_varsFormula_replaceParamWithVarFormula_of_not_mem_and_ne
      (σ := σ) (κ := κ) (a := a) (b := b) (k := k) (φ := φ) hb hba
  calc
    replaceParamWithVarFormula (σ := σ) (κ := κ) k a
        (substFormula (σ := σ) (κ := κ) x (.var b) φ)
        =
      replaceParamWithVarFormula (σ := σ) (κ := κ) k a
        (substFormulaVarNoAlpha (σ := σ) (κ := κ) x b φ) := by
          simp [substFormula_var_eq_noAlpha_of_not_mem_varsFormula (σ := σ) (κ := κ) x b φ hb]
    _ =
      substFormulaVarNoAlpha (σ := σ) (κ := κ) x b
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ) := by
          simpa using replaceParamWithVarFormula_substFormulaVarNoAlpha_comm
            (σ := σ) (κ := κ) k a x b hxa φ
    _ =
      substFormula (σ := σ) (κ := κ) x (.var b)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ) := by
          symm
          simp [substFormula_var_eq_noAlpha_of_not_mem_varsFormula (σ := σ) (κ := κ) x b
            (replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ) hb']

/--
Concrete counterexample showing why
`replaceParamWithVarFormula_substFormula_var_comm_of_not_mem_and_ne` requires
freshness/non-collision side conditions.

Without those hypotheses, commutation can fail because the RHS `substFormula`
may alpha-rename a binder while the LHS side computes through the no-alpha
parameter substitution path before param→var rewriting.
-/
theorem replaceParamWithVarFormula_substFormula_var_comm_counterexample :
    let ψ : FormulaH PUnit Nat := .sigma 0 (.pred () [.var 1, .param 0])
    let k : Nat := 0
    let a : Var := 10
    let x : Var := 1
    let b : Var := 0
    replaceParamWithVarFormula (σ := PUnit) (κ := Nat) k a
        (substFormula (σ := PUnit) (κ := Nat) x (.var b) ψ) ≠
      substFormula (σ := PUnit) (κ := Nat) x (.var b)
        (replaceParamWithVarFormula (σ := PUnit) (κ := Nat) k a ψ) := by
  native_decide

end Henkin
end Syntax
end Noneism
end HeytingLean
