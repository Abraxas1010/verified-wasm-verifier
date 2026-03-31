import HeytingLean.Noneism.ProofTheory.ND
import HeytingLean.Noneism.ProofTheory.Quantifiers.Hygiene
import HeytingLean.Noneism.ProofTheory.Quantifiers.DerivesEFresh

/-!
# Noneism.ProofTheory.Quantifiers.DerivedRules

Derived quantifier rules that package eigenvariable hygiene automatically.

Why this file exists:
- The core `ND.Derives` constructors expose explicit side-conditions.
- For routine proof search and future completeness work, we want "always-applicable" entry points
  that pick a fresh variable deterministically from the current syntactic context.
- This keeps the trusted kernel small (constructors stay explicit) while reducing ad-hoc scripts.
-/

namespace HeytingLean
namespace Noneism
namespace ND

open Formula
open Syntax

variable {σ : Type}

/-! ## Fresh variable helpers for quantifier rules -/

/-- Fresh variable for `pi`-introduction, avoiding both context free vars and formula vars. -/
def freshPiEigen (Γ : List (Formula σ)) (φ : Formula σ) : Var :=
  Syntax.freshVar (ND.fvContext Γ ∪ Syntax.varsFormula φ)

lemma freshPiEigen_not_mem_fvContext (Γ : List (Formula σ)) (φ : Formula σ) :
    freshPiEigen (σ := σ) Γ φ ∉ ND.fvContext Γ := by
  intro hmem
  have hfresh :
      freshPiEigen (σ := σ) Γ φ ∉ ND.fvContext Γ ∪ Syntax.varsFormula φ := by
    simpa [freshPiEigen] using
      (Syntax.freshVar_not_mem (S := ND.fvContext Γ ∪ Syntax.varsFormula φ))
  exact hfresh (Finset.mem_union.2 (Or.inl hmem))

lemma freshPiEigen_not_mem_varsFormula (Γ : List (Formula σ)) (φ : Formula σ) :
    freshPiEigen (σ := σ) Γ φ ∉ Syntax.varsFormula φ := by
  intro hmem
  have hfresh :
      freshPiEigen (σ := σ) Γ φ ∉ ND.fvContext Γ ∪ Syntax.varsFormula φ := by
    simpa [freshPiEigen] using
      (Syntax.freshVar_not_mem (S := ND.fvContext Γ ∪ Syntax.varsFormula φ))
  exact hfresh (Finset.mem_union.2 (Or.inr hmem))

/-- Fresh variable for quantified instantiation, avoiding all variables in the body. -/
def freshInstVar (φ : Formula σ) : Var :=
  Syntax.freshVar (Syntax.varsFormula φ)

lemma freshInstVar_not_mem_varsFormula (φ : Formula σ) :
    freshInstVar (σ := σ) φ ∉ Syntax.varsFormula φ := by
  simpa [freshInstVar] using
    (Syntax.freshVar_not_mem (S := Syntax.varsFormula φ))

/-- Fresh variable for `sigma`-elimination, avoiding context/body/conclusion free vars. -/
def freshSigmaEigen (Γ : List (Formula σ)) (φ χ : Formula σ) : Var :=
  Syntax.freshVar (ND.fvContext Γ ∪ Syntax.varsFormula φ ∪ Syntax.fvFormula χ)

lemma freshSigmaEigen_not_mem_fvContext (Γ : List (Formula σ)) (φ χ : Formula σ) :
    freshSigmaEigen (σ := σ) Γ φ χ ∉ ND.fvContext Γ := by
  intro hmem
  have hfresh :
      freshSigmaEigen (σ := σ) Γ φ χ ∉
        (ND.fvContext Γ ∪ Syntax.varsFormula φ ∪ Syntax.fvFormula χ) := by
    simpa [freshSigmaEigen] using
      (Syntax.freshVar_not_mem
        (S := ND.fvContext Γ ∪ Syntax.varsFormula φ ∪ Syntax.fvFormula χ))
  exact hfresh (Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl hmem))))

lemma freshSigmaEigen_not_mem_varsFormula (Γ : List (Formula σ)) (φ χ : Formula σ) :
    freshSigmaEigen (σ := σ) Γ φ χ ∉ Syntax.varsFormula φ := by
  intro hmem
  have hfresh :
      freshSigmaEigen (σ := σ) Γ φ χ ∉
        (ND.fvContext Γ ∪ Syntax.varsFormula φ ∪ Syntax.fvFormula χ) := by
    simpa [freshSigmaEigen] using
      (Syntax.freshVar_not_mem
        (S := ND.fvContext Γ ∪ Syntax.varsFormula φ ∪ Syntax.fvFormula χ))
  exact hfresh (Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inr hmem))))

lemma freshSigmaEigen_not_mem_fvFormula (Γ : List (Formula σ)) (φ χ : Formula σ) :
    freshSigmaEigen (σ := σ) Γ φ χ ∉ Syntax.fvFormula χ := by
  intro hmem
  have hfresh :
      freshSigmaEigen (σ := σ) Γ φ χ ∉
        (ND.fvContext Γ ∪ Syntax.varsFormula φ ∪ Syntax.fvFormula χ) := by
    simpa [freshSigmaEigen] using
      (Syntax.freshVar_not_mem
        (S := ND.fvContext Γ ∪ Syntax.varsFormula φ ∪ Syntax.fvFormula χ))
  exact hfresh (Finset.mem_union.2 (Or.inr hmem))

/-! ## Derived rules with automatic eigenvariable selection -/

theorem piI_with {Γ : List (Formula σ)} {x a : Var} {φ : Formula σ}
    (haΓ : a ∉ ND.fvContext Γ)
    (haφ : a ∉ Syntax.varsFormula φ)
    (h : Derives Γ (Syntax.substFormula (σ := σ) x (.var a) φ)) :
    Derives Γ (.pi x φ) :=
  Derives.piI haΓ haφ h

theorem piI_auto {Γ : List (Formula σ)} {x : Var} {φ : Formula σ} :
    Derives Γ (Syntax.substFormula (σ := σ) x (.var (freshPiEigen (σ := σ) Γ φ)) φ) →
      Derives Γ (.pi x φ) := by
  intro h
  exact piI_with
    (a := freshPiEigen (σ := σ) Γ φ)
    (x := x)
    (φ := φ)
    (freshPiEigen_not_mem_fvContext (σ := σ) Γ φ)
    (freshPiEigen_not_mem_varsFormula (σ := σ) Γ φ)
    h

/--
`piI_auto` in the no-alpha specialization from `Quantifiers.Hygiene`.

This is often a cleaner goal-shape for automation: no branchy substitution term remains.
-/
theorem piI_auto_noAlpha {Γ : List (Formula σ)} {x : Var} {φ : Formula σ} :
    Derives Γ
      (Syntax.substFormulaVarNoAlpha (σ := σ) x (freshPiEigen (σ := σ) Γ φ) φ) →
    Derives Γ (.pi x φ) := by
  intro h
  have hEq :
      Syntax.substFormula (σ := σ) x (.var (freshPiEigen (σ := σ) Γ φ)) φ =
        Syntax.substFormulaVarNoAlpha (σ := σ) x (freshPiEigen (σ := σ) Γ φ) φ :=
    Syntax.substFormula_var_eq_noAlpha_of_not_mem_varsFormula (σ := σ) x
      (freshPiEigen (σ := σ) Γ φ) φ
      (freshPiEigen_not_mem_varsFormula (σ := σ) Γ φ)
  exact piI_auto (x := x) (φ := φ) (by simpa [hEq] using h)

theorem piE_with {Γ : List (Formula σ)} {x a : Var} {φ : Formula σ}
    (_haφ : a ∉ Syntax.boundVars (σ := σ) φ)
    (h : Derives Γ (.pi x φ)) :
    Derives Γ (Syntax.substFormula (σ := σ) x (.var a) φ) :=
  Derives.piE h

theorem piE_auto {Γ : List (Formula σ)} {x : Var} {φ : Formula σ} :
    Derives Γ (.pi x φ) →
      Derives Γ (Syntax.substFormula (σ := σ) x (.var (freshInstVar (σ := σ) φ)) φ) := by
  intro h
  exact piE_with
    (a := freshInstVar (σ := σ) φ)
    (x := x)
    (φ := φ)
    (Syntax.not_mem_boundVars_of_not_mem_varsFormula (σ := σ)
      (freshInstVar_not_mem_varsFormula (σ := σ) φ))
    h

theorem piE_auto_noAlpha {Γ : List (Formula σ)} {x : Var} {φ : Formula σ} :
    Derives Γ (.pi x φ) →
      Derives Γ
        (Syntax.substFormulaVarNoAlpha (σ := σ) x (freshInstVar (σ := σ) φ) φ) := by
  intro h
  have hEq :
      Syntax.substFormula (σ := σ) x (.var (freshInstVar (σ := σ) φ)) φ =
        Syntax.substFormulaVarNoAlpha (σ := σ) x (freshInstVar (σ := σ) φ) φ :=
    Syntax.substFormula_var_eq_noAlpha_of_not_mem_varsFormula (σ := σ) x
      (freshInstVar (σ := σ) φ) φ
      (freshInstVar_not_mem_varsFormula (σ := σ) φ)
  exact by simpa [hEq] using (piE_auto (x := x) (φ := φ) h)

theorem sigmaI_with {Γ : List (Formula σ)} {x a : Var} {φ : Formula σ}
    (_haφ : a ∉ Syntax.boundVars (σ := σ) φ)
    (h : Derives Γ (Syntax.substFormula (σ := σ) x (.var a) φ)) :
    Derives Γ (.sigma x φ) :=
  Derives.sigmaI h

theorem sigmaI_auto {Γ : List (Formula σ)} {x : Var} {φ : Formula σ} :
    Derives Γ (Syntax.substFormula (σ := σ) x (.var (freshInstVar (σ := σ) φ)) φ) →
      Derives Γ (.sigma x φ) := by
  intro h
  exact sigmaI_with
    (a := freshInstVar (σ := σ) φ)
    (x := x)
    (φ := φ)
    (Syntax.not_mem_boundVars_of_not_mem_varsFormula (σ := σ)
      (freshInstVar_not_mem_varsFormula (σ := σ) φ))
    h

theorem sigmaI_auto_noAlpha {Γ : List (Formula σ)} {x : Var} {φ : Formula σ} :
    Derives Γ
      (Syntax.substFormulaVarNoAlpha (σ := σ) x (freshInstVar (σ := σ) φ) φ) →
      Derives Γ (.sigma x φ) := by
  intro h
  have hEq :
      Syntax.substFormula (σ := σ) x (.var (freshInstVar (σ := σ) φ)) φ =
        Syntax.substFormulaVarNoAlpha (σ := σ) x (freshInstVar (σ := σ) φ) φ :=
    Syntax.substFormula_var_eq_noAlpha_of_not_mem_varsFormula (σ := σ) x
      (freshInstVar (σ := σ) φ) φ
      (freshInstVar_not_mem_varsFormula (σ := σ) φ)
  exact sigmaI_auto (x := x) (φ := φ) (by simpa [hEq] using h)

theorem sigmaE_with {Γ : List (Formula σ)} {x a : Var} {φ χ : Formula σ}
    (hs : Derives Γ (.sigma x φ))
    (haΓ : a ∉ ND.fvContext Γ)
    (haφ : a ∉ Syntax.varsFormula φ)
    (haχ : a ∉ Syntax.fvFormula χ)
    (hder : Derives (Syntax.substFormula (σ := σ) x (.var a) φ :: Γ) χ) :
    Derives Γ χ :=
  Derives.sigmaE hs haΓ haφ haχ hder

theorem sigmaE_auto {Γ : List (Formula σ)} {x : Var} {φ χ : Formula σ} :
    Derives Γ (.sigma x φ) →
      Derives
        (Syntax.substFormula (σ := σ) x (.var (freshSigmaEigen (σ := σ) Γ φ χ)) φ :: Γ)
        χ →
      Derives Γ χ := by
  intro hs hder
  exact sigmaE_with
    (a := freshSigmaEigen (σ := σ) Γ φ χ)
    (x := x)
    (φ := φ)
    (χ := χ)
    hs
    (freshSigmaEigen_not_mem_fvContext (σ := σ) Γ φ χ)
    (freshSigmaEigen_not_mem_varsFormula (σ := σ) Γ φ χ)
    (freshSigmaEigen_not_mem_fvFormula (σ := σ) Γ φ χ)
    hder

/--
Transport a witness-instance derivation from witness `a` to witness `b` in a fixed context.

This is the core syntactic witness-renaming step used by internal FO completeness.
-/
theorem derives_witness_change
    {Γ : List (Formula σ)} {x a b : Var} {φ χ : Formula σ}
    (haΓ : a ∉ ND.fvContext (σ := σ) Γ)
    (haVars : a ∉ Syntax.varsFormula (σ := σ) φ)
    (hbVars : b ∉ Syntax.varsFormula (σ := σ) φ)
    (hab : a ≠ b)
    (haχ : a ∉ Syntax.fvFormula (σ := σ) χ)
    (hDer : Derives (σ := σ) (Syntax.substFormula (σ := σ) x (.var a) φ :: Γ) χ) :
    Derives (σ := σ) (Syntax.substFormula (σ := σ) x (.var b) φ :: Γ) χ := by
  let θa : Formula σ := Syntax.substFormula (σ := σ) x (.var a) φ
  let θb : Formula σ := Syntax.substFormula (σ := σ) x (.var b) φ
  have hbBound : b ∉ Syntax.boundVars (σ := σ) φ :=
    Syntax.not_mem_boundVars_of_not_mem_varsFormula (σ := σ) hbVars
  have hSigmaB : Derives (σ := σ) (θb :: Γ) (.sigma x φ) := by
    exact Derives.sigmaI (x := x) (a := b) (φ := φ) (Derives.hyp (by simp [θb]))
  have hSubCtx : (θa :: Γ) ⊆ (θa :: θb :: Γ) := by
    intro t ht
    rcases List.mem_cons.1 ht with rfl | htail
    · simp
    · exact by simp [htail]
  have hDerLift : Derives (σ := σ) (θa :: θb :: Γ) χ :=
    Derives.wk hDer hSubCtx
  have haθb : a ∉ Syntax.fvFormula (σ := σ) θb := by
    simpa [θb] using
      (Syntax.not_mem_fvFormula_substFormula_var_of_not_mem_varsFormula
        (σ := σ) x a b φ haVars hbVars hab)
  have haCtx : a ∉ ND.fvContext (σ := σ) (θb :: Γ) := by
    intro haMem
    have hsplit :
        a ∈ Syntax.fvFormula (σ := σ) θb ∨ a ∈ ND.fvContext (σ := σ) Γ := by
      simpa [ND.fvContext] using haMem
    rcases hsplit with hθb | hΓ
    · exact haθb hθb
    · exact haΓ hΓ
  exact Derives.sigmaE hSigmaB haCtx haVars haχ hDerLift

/--
Normalize a witness-instance derivation to one using the canonical fresh sigma-eigen variable.
-/
theorem derives_witness_change_to_freshSigmaEigen
    {Γ : List (Formula σ)} {x a : Var} {φ χ : Formula σ}
    (haΓ : a ∉ ND.fvContext (σ := σ) Γ)
    (haVars : a ∉ Syntax.varsFormula (σ := σ) φ)
    (haχ : a ∉ Syntax.fvFormula (σ := σ) χ)
    (hDer : Derives (σ := σ) (Syntax.substFormula (σ := σ) x (.var a) φ :: Γ) χ) :
    ∃ b : Var,
      b ∉ ND.fvContext (σ := σ) Γ ∧
      b ∉ Syntax.varsFormula (σ := σ) φ ∧
      b ∉ Syntax.fvFormula (σ := σ) χ ∧
      Derives (σ := σ) (Syntax.substFormula (σ := σ) x (.var b) φ :: Γ) χ := by
  let b : Var := freshSigmaEigen (σ := σ) Γ φ χ
  have hbΓ : b ∉ ND.fvContext (σ := σ) Γ :=
    freshSigmaEigen_not_mem_fvContext (σ := σ) Γ φ χ
  have hbVars : b ∉ Syntax.varsFormula (σ := σ) φ :=
    freshSigmaEigen_not_mem_varsFormula (σ := σ) Γ φ χ
  have hbχ : b ∉ Syntax.fvFormula (σ := σ) χ :=
    freshSigmaEigen_not_mem_fvFormula (σ := σ) Γ φ χ
  by_cases hEq : b = a
  · subst hEq
    exact ⟨b, hbΓ, hbVars, hbχ, hDer⟩
  ·
    have hDer' :
        Derives (σ := σ) (Syntax.substFormula (σ := σ) x (.var b) φ :: Γ) χ :=
      derives_witness_change
        (σ := σ) (Γ := Γ) (x := x) (a := a) (b := b) (φ := φ) (χ := χ)
        haΓ haVars hbVars (Ne.symm hEq) haχ hDer
    exact ⟨b, hbΓ, hbVars, hbχ, hDer'⟩

theorem piI_exists {Γ : List (Formula σ)} {x : Var} {φ : Formula σ} :
    (∃ a : Var,
      a ∉ ND.fvContext Γ ∧
      a ∉ Syntax.varsFormula φ ∧
      Derives Γ (Syntax.substFormula (σ := σ) x (.var a) φ)) →
    Derives Γ (.pi x φ) := by
  rintro ⟨a, haΓ, haφ, h⟩
  exact piI_with (x := x) (a := a) (φ := φ) haΓ haφ h

theorem piE_exists {Γ : List (Formula σ)} {x : Var} {φ : Formula σ} :
    Derives Γ (.pi x φ) →
    ∃ a : Var, a ∉ Syntax.boundVars (σ := σ) φ ∧
      Derives Γ (Syntax.substFormula (σ := σ) x (.var a) φ) := by
  intro h
  exact ⟨freshInstVar (σ := σ) φ,
    Syntax.not_mem_boundVars_of_not_mem_varsFormula (σ := σ)
      (freshInstVar_not_mem_varsFormula (σ := σ) φ),
    piE_auto (x := x) (φ := φ) h⟩

theorem sigmaI_exists {Γ : List (Formula σ)} {x : Var} {φ : Formula σ} :
    (∃ a : Var, a ∉ Syntax.boundVars (σ := σ) φ ∧
      Derives Γ (Syntax.substFormula (σ := σ) x (.var a) φ)) →
    Derives Γ (.sigma x φ) := by
  rintro ⟨a, haφ, h⟩
  exact sigmaI_with (x := x) (a := a) (φ := φ) haφ h

theorem sigmaE_exists {Γ : List (Formula σ)} {x : Var} {φ χ : Formula σ} :
    Derives Γ (.sigma x φ) →
    (∃ a : Var,
      a ∉ ND.fvContext Γ ∧
      a ∉ Syntax.varsFormula φ ∧
      a ∉ Syntax.fvFormula χ ∧
      Derives (Syntax.substFormula (σ := σ) x (.var a) φ :: Γ) χ) →
    Derives Γ χ := by
  intro hs
  rintro ⟨a, haΓ, haφ, haχ, hder⟩
  exact sigmaE_with (x := x) (a := a) (φ := φ) (χ := χ) hs haΓ haφ haχ hder

end ND
end Noneism
end HeytingLean
