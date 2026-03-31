import HeytingLean.Noneism.ProofTheory.Quantifiers.NDHVarSupport

namespace HeytingLean
namespace Noneism
namespace NDH

open Syntax.Henkin

/-!
Derived rules for `NDH.Derives` over Henkin formulas (`FormulaH`).

This mirrors the base-language derived rules in
`HeytingLean.Noneism.ProofTheory.Quantifiers.DerivedRules`, but specialized to the
Henkin syntax and judgment.
-/

section

variable {σ κ : Type}

/-- A fresh pi-eigenvariable avoiding the context and the quantified body. -/
def freshPiEigenH (Γ : List (FormulaH σ κ)) (φ : FormulaH σ κ) : Var :=
  Syntax.freshVar (fvContext (σ := σ) (κ := κ) Γ ∪ varsFormula (σ := σ) (κ := κ) φ)

lemma freshPiEigenH_not_mem_fvContext
    (Γ : List (FormulaH σ κ)) (φ : FormulaH σ κ) :
    freshPiEigenH (σ := σ) (κ := κ) Γ φ ∉ fvContext (σ := σ) (κ := κ) Γ := by
  let avoid : Finset Var :=
    fvContext (σ := σ) (κ := κ) Γ ∪ varsFormula (σ := σ) (κ := κ) φ
  have hnot : Syntax.freshVar avoid ∉ avoid := Syntax.freshVar_not_mem avoid
  intro hmem
  have : Syntax.freshVar avoid ∈ avoid := by
    refine Finset.mem_union.2 (Or.inl ?_)
    simpa [freshPiEigenH, avoid] using hmem
  exact hnot this

lemma freshPiEigenH_not_mem_varsFormula
    (Γ : List (FormulaH σ κ)) (φ : FormulaH σ κ) :
    freshPiEigenH (σ := σ) (κ := κ) Γ φ ∉ varsFormula (σ := σ) (κ := κ) φ := by
  let avoid : Finset Var :=
    fvContext (σ := σ) (κ := κ) Γ ∪ varsFormula (σ := σ) (κ := κ) φ
  have hnot : Syntax.freshVar avoid ∉ avoid := Syntax.freshVar_not_mem avoid
  intro hmem
  have : Syntax.freshVar avoid ∈ avoid := by
    refine Finset.mem_union.2 (Or.inr ?_)
    simpa [freshPiEigenH, avoid] using hmem
  exact hnot this

/-- A fresh variable avoiding all vars of a formula (useful for pi/sigma instantiation). -/
def freshInstVarH (φ : FormulaH σ κ) : Var :=
  Syntax.freshVar (varsFormula (σ := σ) (κ := κ) φ)

lemma freshInstVarH_not_mem_varsFormula (φ : FormulaH σ κ) :
    freshInstVarH (σ := σ) (κ := κ) φ ∉ varsFormula (σ := σ) (κ := κ) φ := by
  simpa [freshInstVarH] using
    (Syntax.freshVar_not_mem (varsFormula (σ := σ) (κ := κ) φ))

theorem piI_with {Γ : List (FormulaH σ κ)} {x a : Var} {φ : FormulaH σ κ}
    (haΓ : a ∉ fvContext (σ := σ) (κ := κ) Γ)
    (haφ : a ∉ varsFormula (σ := σ) (κ := κ) φ)
    (h : Derives (σ := σ) (κ := κ) Γ
      (substFormula (σ := σ) (κ := κ) x (.var a) φ)) :
    Derives (σ := σ) (κ := κ) Γ (.pi x φ) :=
  Derives.piI haΓ haφ h

theorem piI_auto {Γ : List (FormulaH σ κ)} {x : Var} {φ : FormulaH σ κ} :
    Derives (σ := σ) (κ := κ) Γ
      (substFormula (σ := σ) (κ := κ) x
        (.var (freshPiEigenH (σ := σ) (κ := κ) Γ φ)) φ) →
      Derives (σ := σ) (κ := κ) Γ (.pi x φ) := by
  intro h
  exact piI_with
    (σ := σ) (κ := κ)
    (a := freshPiEigenH (σ := σ) (κ := κ) Γ φ)
    (x := x) (φ := φ)
    (freshPiEigenH_not_mem_fvContext (σ := σ) (κ := κ) Γ φ)
    (freshPiEigenH_not_mem_varsFormula (σ := σ) (κ := κ) Γ φ)
    h

theorem piE_with {Γ : List (FormulaH σ κ)} {x a : Var} {φ : FormulaH σ κ}
    (_haφ : a ∉ boundVars (σ := σ) (κ := κ) φ)
    (h : Derives (σ := σ) (κ := κ) Γ (.pi x φ)) :
    Derives (σ := σ) (κ := κ) Γ
      (substFormula (σ := σ) (κ := κ) x (.var a) φ) :=
  Derives.piE (x := x) (t := .var a) (φ := φ) h

theorem piE_auto {Γ : List (FormulaH σ κ)} {x : Var} {φ : FormulaH σ κ} :
    Derives (σ := σ) (κ := κ) Γ (.pi x φ) →
      Derives (σ := σ) (κ := κ) Γ
        (substFormula (σ := σ) (κ := κ) x
          (.var (freshInstVarH (σ := σ) (κ := κ) φ)) φ) := by
  intro h
  exact piE_with
    (σ := σ) (κ := κ)
    (a := freshInstVarH (σ := σ) (κ := κ) φ)
    (x := x) (φ := φ)
    (not_mem_boundVars_of_not_mem_varsFormula
      (σ := σ) (κ := κ)
      (freshInstVarH_not_mem_varsFormula (σ := σ) (κ := κ) φ))
    h

theorem sigmaI_with {Γ : List (FormulaH σ κ)} {x a : Var} {φ : FormulaH σ κ}
    (_haφ : a ∉ boundVars (σ := σ) (κ := κ) φ)
    (h : Derives (σ := σ) (κ := κ) Γ
      (substFormula (σ := σ) (κ := κ) x (.var a) φ)) :
    Derives (σ := σ) (κ := κ) Γ (.sigma x φ) :=
  Derives.sigmaI (x := x) (t := .var a) (φ := φ) h

theorem sigmaI_auto {Γ : List (FormulaH σ κ)} {x : Var} {φ : FormulaH σ κ} :
    Derives (σ := σ) (κ := κ) Γ
      (substFormula (σ := σ) (κ := κ) x
        (.var (freshInstVarH (σ := σ) (κ := κ) φ)) φ) →
      Derives (σ := σ) (κ := κ) Γ (.sigma x φ) := by
  intro h
  exact sigmaI_with
    (σ := σ) (κ := κ)
    (a := freshInstVarH (σ := σ) (κ := κ) φ)
    (x := x) (φ := φ)
    (not_mem_boundVars_of_not_mem_varsFormula
      (σ := σ) (κ := κ)
      (freshInstVarH_not_mem_varsFormula (σ := σ) (κ := κ) φ))
    h

theorem derives_pi_instance_change
    {Γ : List (FormulaH σ κ)} {x a b : Var} {φ : FormulaH σ κ}
    (haΓ : a ∉ fvContext (σ := σ) (κ := κ) Γ)
    (haVars : a ∉ varsFormula (σ := σ) (κ := κ) φ)
    (hDer :
      Derives (σ := σ) (κ := κ) Γ
        (substFormula (σ := σ) (κ := κ) x (.var a) φ)) :
    Derives (σ := σ) (κ := κ) Γ
      (substFormula (σ := σ) (κ := κ) x (.var b) φ) := by
  have hPi : Derives (σ := σ) (κ := κ) Γ (.pi x φ) :=
    Derives.piI haΓ haVars hDer
  exact Derives.piE (x := x) (t := .var b) (φ := φ) hPi

theorem derives_pi_instance_change_to_freshInstVarH
    {Γ : List (FormulaH σ κ)} {x a : Var} {φ : FormulaH σ κ}
    (haΓ : a ∉ fvContext (σ := σ) (κ := κ) Γ)
    (haVars : a ∉ varsFormula (σ := σ) (κ := κ) φ)
    (hDer :
      Derives (σ := σ) (κ := κ) Γ
        (substFormula (σ := σ) (κ := κ) x (.var a) φ)) :
    ∃ b : Var,
      b ∉ varsFormula (σ := σ) (κ := κ) φ ∧
      Derives (σ := σ) (κ := κ) Γ
        (substFormula (σ := σ) (κ := κ) x (.var b) φ) := by
  let b : Var := freshInstVarH (σ := σ) (κ := κ) φ
  have hbVars : b ∉ varsFormula (σ := σ) (κ := κ) φ :=
    freshInstVarH_not_mem_varsFormula (σ := σ) (κ := κ) φ
  exact ⟨b, hbVars,
    derives_pi_instance_change
      (σ := σ) (κ := κ) (Γ := Γ) (x := x) (a := a) (b := b) (φ := φ)
      haΓ haVars hDer⟩

/-- A fresh sigma-eigenvariable avoiding the context, the quantifier body, and the goal. -/
def freshSigmaEigenH (Γ : List (FormulaH σ κ)) (φ χ : FormulaH σ κ) : Var :=
  Syntax.freshVar
    ((fvContext (σ := σ) (κ := κ) Γ ∪ varsFormula (σ := σ) (κ := κ) φ) ∪
      fvFormula (σ := σ) (κ := κ) χ)

lemma freshSigmaEigenH_not_mem_fvContext
    (Γ : List (FormulaH σ κ)) (φ χ : FormulaH σ κ) :
    freshSigmaEigenH (σ := σ) (κ := κ) Γ φ χ ∉ fvContext (σ := σ) (κ := κ) Γ := by
  let avoid : Finset Var :=
    (fvContext (σ := σ) (κ := κ) Γ ∪ varsFormula (σ := σ) (κ := κ) φ) ∪
      fvFormula (σ := σ) (κ := κ) χ
  have hnot : Syntax.freshVar avoid ∉ avoid := Syntax.freshVar_not_mem avoid
  intro hmem
  have : Syntax.freshVar avoid ∈ avoid := by
    refine Finset.mem_union.2 (Or.inl ?_)
    refine Finset.mem_union.2 (Or.inl ?_)
    simpa [freshSigmaEigenH, avoid] using hmem
  exact hnot this

lemma freshSigmaEigenH_not_mem_varsFormula
    (Γ : List (FormulaH σ κ)) (φ χ : FormulaH σ κ) :
    freshSigmaEigenH (σ := σ) (κ := κ) Γ φ χ ∉ varsFormula (σ := σ) (κ := κ) φ := by
  let avoid : Finset Var :=
    (fvContext (σ := σ) (κ := κ) Γ ∪ varsFormula (σ := σ) (κ := κ) φ) ∪
      fvFormula (σ := σ) (κ := κ) χ
  have hnot : Syntax.freshVar avoid ∉ avoid := Syntax.freshVar_not_mem avoid
  intro hmem
  have : Syntax.freshVar avoid ∈ avoid := by
    refine Finset.mem_union.2 (Or.inl ?_)
    refine Finset.mem_union.2 (Or.inr ?_)
    simpa [freshSigmaEigenH, avoid] using hmem
  exact hnot this

lemma freshSigmaEigenH_not_mem_fvFormula
    (Γ : List (FormulaH σ κ)) (φ χ : FormulaH σ κ) :
    freshSigmaEigenH (σ := σ) (κ := κ) Γ φ χ ∉ fvFormula (σ := σ) (κ := κ) χ := by
  let avoid : Finset Var :=
    (fvContext (σ := σ) (κ := κ) Γ ∪ varsFormula (σ := σ) (κ := κ) φ) ∪
      fvFormula (σ := σ) (κ := κ) χ
  have hnot : Syntax.freshVar avoid ∉ avoid := Syntax.freshVar_not_mem avoid
  intro hmem
  have : Syntax.freshVar avoid ∈ avoid := by
    refine Finset.mem_union.2 (Or.inr ?_)
    simpa [freshSigmaEigenH, avoid] using hmem
  exact hnot this

theorem sigmaE_with {Γ : List (FormulaH σ κ)} {x a : Var} {φ χ : FormulaH σ κ}
    (hs : Derives (σ := σ) (κ := κ) Γ (.sigma x φ))
    (haΓ : a ∉ fvContext (σ := σ) (κ := κ) Γ)
    (haφ : a ∉ varsFormula (σ := σ) (κ := κ) φ)
    (haχ : a ∉ fvFormula (σ := σ) (κ := κ) χ)
    (hder :
      Derives (σ := σ) (κ := κ)
        (substFormula (σ := σ) (κ := κ) x (.var a) φ :: Γ) χ) :
    Derives (σ := σ) (κ := κ) Γ χ :=
  Derives.sigmaE hs haΓ haφ haχ hder

theorem sigmaE_auto {Γ : List (FormulaH σ κ)} {x : Var} {φ χ : FormulaH σ κ} :
    Derives (σ := σ) (κ := κ) Γ (.sigma x φ) →
      Derives (σ := σ) (κ := κ)
        (substFormula (σ := σ) (κ := κ) x
          (.var (freshSigmaEigenH (σ := σ) (κ := κ) Γ φ χ)) φ :: Γ)
        χ →
      Derives (σ := σ) (κ := κ) Γ χ := by
  intro hs hder
  exact sigmaE_with
    (σ := σ) (κ := κ) (x := x)
    (a := freshSigmaEigenH (σ := σ) (κ := κ) Γ φ χ)
    (φ := φ) (χ := χ)
    hs
    (freshSigmaEigenH_not_mem_fvContext (σ := σ) (κ := κ) Γ φ χ)
    (freshSigmaEigenH_not_mem_varsFormula (σ := σ) (κ := κ) Γ φ χ)
    (freshSigmaEigenH_not_mem_fvFormula (σ := σ) (κ := κ) Γ φ χ)
    hder

theorem derives_witness_change
    [DecidableEq κ]
    {Γ : List (FormulaH σ κ)} {x a b : Var} {φ χ : FormulaH σ κ}
    (haΓ : a ∉ fvContext (σ := σ) (κ := κ) Γ)
    (haVars : a ∉ varsFormula (σ := σ) (κ := κ) φ)
    (hbVars : b ∉ varsFormula (σ := σ) (κ := κ) φ)
    (hab : a ≠ b)
    (haχ : a ∉ fvFormula (σ := σ) (κ := κ) χ)
    (hDer :
      Derives (σ := σ) (κ := κ)
        (substFormula (σ := σ) (κ := κ) x (.var a) φ :: Γ) χ) :
    Derives (σ := σ) (κ := κ)
      (substFormula (σ := σ) (κ := κ) x (.var b) φ :: Γ) χ := by
  let θa : FormulaH σ κ := substFormula (σ := σ) (κ := κ) x (.var a) φ
  let θb : FormulaH σ κ := substFormula (σ := σ) (κ := κ) x (.var b) φ
  have hSigmaB :
      Derives (σ := σ) (κ := κ) (θb :: Γ) (.sigma x φ) := by
    exact Derives.sigmaI (x := x) (t := .var b) (φ := φ)
      (Derives.hyp (by simp [θb]))
  have hSubCtx : (θa :: Γ) ⊆ (θa :: θb :: Γ) := by
    intro t ht
    rcases List.mem_cons.1 ht with rfl | htail
    · simp
    · exact by simp [htail]
  have hDerLift :
      Derives (σ := σ) (κ := κ) (θa :: θb :: Γ) χ :=
    Derives.wk hDer hSubCtx
  have haθbVars :
      a ∉ varsFormula (σ := σ) (κ := κ) θb := by
    simpa [θb] using
      (not_mem_varsFormula_substFormula_var_of_not_mem_and_ne
        (σ := σ) (κ := κ) (a := a) (b := b) (x := x) (φ := φ)
        haVars hab hbVars)
  have haθb :
      a ∉ fvFormula (σ := σ) (κ := κ) θb := by
    intro haMem
    exact haθbVars
      ((fvFormula_subset_varsFormula (σ := σ) (κ := κ) θb) haMem)
  have haCtx : a ∉ fvContext (σ := σ) (κ := κ) (θb :: Γ) := by
    intro haMem
    have hsplit :
        a ∈ fvFormula (σ := σ) (κ := κ) θb ∨
          a ∈ fvContext (σ := σ) (κ := κ) Γ := by
      simpa [fvContext_cons, Finset.mem_union] using haMem
    rcases hsplit with hθb | hΓ
    · exact haθb hθb
    · exact haΓ hΓ
  exact Derives.sigmaE hSigmaB haCtx haVars haχ hDerLift

theorem derives_witness_change_to_freshSigmaEigen
    [DecidableEq κ]
    {Γ : List (FormulaH σ κ)} {x a : Var} {φ χ : FormulaH σ κ}
    (haΓ : a ∉ fvContext (σ := σ) (κ := κ) Γ)
    (haVars : a ∉ varsFormula (σ := σ) (κ := κ) φ)
    (haχ : a ∉ fvFormula (σ := σ) (κ := κ) χ)
    (hDer :
      Derives (σ := σ) (κ := κ)
        (substFormula (σ := σ) (κ := κ) x (.var a) φ :: Γ) χ) :
    ∃ b : Var,
      b ∉ fvContext (σ := σ) (κ := κ) Γ ∧
      b ∉ varsFormula (σ := σ) (κ := κ) φ ∧
      b ∉ fvFormula (σ := σ) (κ := κ) χ ∧
      Derives (σ := σ) (κ := κ)
        (substFormula (σ := σ) (κ := κ) x (.var b) φ :: Γ) χ := by
  let b : Var := freshSigmaEigenH (σ := σ) (κ := κ) Γ φ χ
  have hbΓ : b ∉ fvContext (σ := σ) (κ := κ) Γ :=
    freshSigmaEigenH_not_mem_fvContext (σ := σ) (κ := κ) Γ φ χ
  have hbVars : b ∉ varsFormula (σ := σ) (κ := κ) φ :=
    freshSigmaEigenH_not_mem_varsFormula (σ := σ) (κ := κ) Γ φ χ
  have hbχ : b ∉ fvFormula (σ := σ) (κ := κ) χ :=
    freshSigmaEigenH_not_mem_fvFormula (σ := σ) (κ := κ) Γ φ χ
  by_cases hEq : b = a
  · subst hEq
    exact ⟨b, hbΓ, hbVars, hbχ, hDer⟩
  ·
    have hDer' :
        Derives (σ := σ) (κ := κ)
          (substFormula (σ := σ) (κ := κ) x (.var b) φ :: Γ) χ :=
      derives_witness_change
        (σ := σ) (κ := κ) (Γ := Γ) (x := x) (a := a) (b := b) (φ := φ) (χ := χ)
        haΓ haVars hbVars (Ne.symm hEq) haχ hDer
    exact ⟨b, hbΓ, hbVars, hbχ, hDer'⟩

theorem piI_exists {Γ : List (FormulaH σ κ)} {x : Var} {φ : FormulaH σ κ} :
    (∃ a : Var,
      a ∉ fvContext (σ := σ) (κ := κ) Γ ∧
      a ∉ varsFormula (σ := σ) (κ := κ) φ ∧
      Derives (σ := σ) (κ := κ) Γ
        (substFormula (σ := σ) (κ := κ) x (.var a) φ)) →
    Derives (σ := σ) (κ := κ) Γ (.pi x φ) := by
  rintro ⟨a, haΓ, haφ, h⟩
  exact piI_with (σ := σ) (κ := κ) (x := x) (a := a) (φ := φ) haΓ haφ h

theorem piE_exists {Γ : List (FormulaH σ κ)} {x : Var} {φ : FormulaH σ κ} :
    Derives (σ := σ) (κ := κ) Γ (.pi x φ) →
    ∃ a : Var, a ∉ boundVars (σ := σ) (κ := κ) φ ∧
      Derives (σ := σ) (κ := κ) Γ
        (substFormula (σ := σ) (κ := κ) x (.var a) φ) := by
  intro h
  exact ⟨freshInstVarH (σ := σ) (κ := κ) φ,
    not_mem_boundVars_of_not_mem_varsFormula
      (σ := σ) (κ := κ)
      (freshInstVarH_not_mem_varsFormula (σ := σ) (κ := κ) φ),
    piE_auto (σ := σ) (κ := κ) (x := x) (φ := φ) h⟩

theorem sigmaI_exists {Γ : List (FormulaH σ κ)} {x : Var} {φ : FormulaH σ κ} :
    (∃ a : Var, a ∉ boundVars (σ := σ) (κ := κ) φ ∧
      Derives (σ := σ) (κ := κ) Γ
        (substFormula (σ := σ) (κ := κ) x (.var a) φ)) →
    Derives (σ := σ) (κ := κ) Γ (.sigma x φ) := by
  rintro ⟨a, haφ, h⟩
  exact sigmaI_with (σ := σ) (κ := κ) (x := x) (a := a) (φ := φ) haφ h

theorem sigmaE_exists {Γ : List (FormulaH σ κ)} {x : Var} {φ χ : FormulaH σ κ} :
    Derives (σ := σ) (κ := κ) Γ (.sigma x φ) →
    (∃ a : Var,
      a ∉ fvContext (σ := σ) (κ := κ) Γ ∧
      a ∉ varsFormula (σ := σ) (κ := κ) φ ∧
      a ∉ fvFormula (σ := σ) (κ := κ) χ ∧
      Derives (σ := σ) (κ := κ)
        (substFormula (σ := σ) (κ := κ) x (.var a) φ :: Γ) χ) →
    Derives (σ := σ) (κ := κ) Γ χ := by
  intro hs
  rintro ⟨a, haΓ, haφ, haχ, hder⟩
  exact sigmaE_with
    (σ := σ) (κ := κ) (x := x) (a := a) (φ := φ) (χ := χ)
    hs haΓ haφ haχ hder

end

end NDH
end Noneism
end HeytingLean
