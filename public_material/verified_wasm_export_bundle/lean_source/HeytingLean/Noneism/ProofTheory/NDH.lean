import HeytingLean.Noneism.Syntax.Henkin
import HeytingLean.Noneism.Syntax.HenkinLiftSubst
import HeytingLean.Noneism.ProofTheory.ND

namespace HeytingLean
namespace Noneism
namespace NDH

open Formula
open Syntax.Henkin

/-- Free-variable support of a Henkin-context. -/
def fvContext {σ κ : Type} (Γ : List (FormulaH σ κ)) : Finset Var :=
  Γ.foldr (fun φ acc => Syntax.Henkin.fvFormula φ ∪ acc) ∅

@[simp] theorem fvContext_nil {σ κ : Type} :
    fvContext (σ := σ) (κ := κ) ([] : List (FormulaH σ κ)) = ∅ := rfl

@[simp] theorem fvContext_cons {σ κ : Type} (φ : FormulaH σ κ) (Γ : List (FormulaH σ κ)) :
    fvContext (σ := σ) (κ := κ) (φ :: Γ) =
      Syntax.Henkin.fvFormula φ ∪ fvContext (σ := σ) (κ := κ) Γ := by
  simp [fvContext]

theorem mem_fvContext_iff {σ κ : Type} {x : Var} {Γ : List (FormulaH σ κ)} :
    x ∈ fvContext (σ := σ) (κ := κ) Γ ↔
      ∃ ψ, ψ ∈ Γ ∧ x ∈ Syntax.Henkin.fvFormula ψ := by
  induction Γ with
  | nil =>
      simp [fvContext]
  | cons φ Γ ih =>
      simp [fvContext_cons, ih]

/-- Map Henkin parameters across a context. -/
def mapParamsContext {σ κ κ' : Type} (f : κ → κ') (Γ : List (FormulaH σ κ)) : List (FormulaH σ κ') :=
  Γ.map (Syntax.Henkin.mapParamsFormula (σ := σ) f)

@[simp] theorem fvContext_mapParamsContext {σ κ κ' : Type} (f : κ → κ') (Γ : List (FormulaH σ κ)) :
    fvContext (σ := σ) (κ := κ') (mapParamsContext (σ := σ) f Γ) =
      fvContext (σ := σ) (κ := κ) Γ := by
  induction Γ with
  | nil =>
      rfl
  | cons φ Γ ih =>
      have ih' : fvContext (σ := σ) (κ := κ') (List.map (Syntax.Henkin.mapParamsFormula (σ := σ) f) Γ) =
          fvContext (σ := σ) (κ := κ) Γ := by
        simpa [mapParamsContext] using ih
      simp [fvContext_cons, mapParamsContext, Syntax.Henkin.fvFormula_mapParamsFormula, ih']

/--
Natural-deduction derivability for Henkin formulas.

This mirrors `Noneism.Derives`, but over `FormulaH` with parameter terms.
Eigenvariable side-conditions are still on `Var`; parameters are not variables.
-/
inductive Derives {σ κ : Type} : List (FormulaH σ κ) → FormulaH σ κ → Prop
  | hyp {Γ : List (FormulaH σ κ)} {φ : FormulaH σ κ} :
      φ ∈ Γ → Derives Γ φ
  | topI {Γ : List (FormulaH σ κ)} :
      Derives Γ .top
  | botE {Γ : List (FormulaH σ κ)} {φ : FormulaH σ κ} :
      Derives Γ .bot → Derives Γ φ
  | andI {Γ : List (FormulaH σ κ)} {φ ψ : FormulaH σ κ} :
      Derives Γ φ → Derives Γ ψ → Derives Γ (.and φ ψ)
  | andEL {Γ : List (FormulaH σ κ)} {φ ψ : FormulaH σ κ} :
      Derives Γ (.and φ ψ) → Derives Γ φ
  | andER {Γ : List (FormulaH σ κ)} {φ ψ : FormulaH σ κ} :
      Derives Γ (.and φ ψ) → Derives Γ ψ
  | orIL {Γ : List (FormulaH σ κ)} {φ ψ : FormulaH σ κ} :
      Derives Γ φ → Derives Γ (.or φ ψ)
  | orIR {Γ : List (FormulaH σ κ)} {φ ψ : FormulaH σ κ} :
      Derives Γ ψ → Derives Γ (.or φ ψ)
  | orE {Γ : List (FormulaH σ κ)} {φ ψ χ : FormulaH σ κ} :
      Derives Γ (.or φ ψ) →
      Derives (φ :: Γ) χ →
      Derives (ψ :: Γ) χ →
      Derives Γ χ
  | impI {Γ : List (FormulaH σ κ)} {φ ψ : FormulaH σ κ} :
      Derives (φ :: Γ) ψ → Derives Γ (.imp φ ψ)
  | impE {Γ : List (FormulaH σ κ)} {φ ψ : FormulaH σ κ} :
      Derives Γ (.imp φ ψ) → Derives Γ φ → Derives Γ ψ
  | notI {Γ : List (FormulaH σ κ)} {φ : FormulaH σ κ} :
      Derives (φ :: Γ) .bot → Derives Γ (.not φ)
  | notE {Γ : List (FormulaH σ κ)} {φ : FormulaH σ κ} :
      Derives Γ (.not φ) → Derives Γ φ → Derives Γ .bot
  | piI {Γ : List (FormulaH σ κ)} {x a : Var} {φ : FormulaH σ κ} :
      a ∉ fvContext (σ := σ) (κ := κ) Γ →
      a ∉ Syntax.Henkin.varsFormula (σ := σ) (κ := κ) φ →
      Derives Γ (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x (.var a) φ) →
      Derives Γ (.pi x φ)
  | piE {Γ : List (FormulaH σ κ)} {x : Var} {t : TermH κ} {φ : FormulaH σ κ} :
      Derives Γ (.pi x φ) →
      Derives Γ (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ)
  | sigmaI {Γ : List (FormulaH σ κ)} {x : Var} {t : TermH κ} {φ : FormulaH σ κ} :
      Derives Γ (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ) →
      Derives Γ (.sigma x φ)
  | sigmaE {Γ : List (FormulaH σ κ)} {x a : Var} {φ χ : FormulaH σ κ} :
      Derives Γ (.sigma x φ) →
      a ∉ fvContext (σ := σ) (κ := κ) Γ →
      a ∉ Syntax.Henkin.varsFormula (σ := σ) (κ := κ) φ →
      a ∉ Syntax.Henkin.fvFormula (σ := σ) (κ := κ) χ →
      Derives (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x (.var a) φ :: Γ) χ →
      Derives Γ χ
  | wk {Γ Δ : List (FormulaH σ κ)} {φ : FormulaH σ κ} :
      Derives Γ φ →
      Γ ⊆ Δ →
      Derives Δ φ

namespace Derives

/--
Parameter renaming is admissible for `NDH.Derives`.

This is the key syntactic tool for "Henkin witness freshness" arguments: it lets us
rename finitely many witness parameters used in a derivation without affecting the
variable eigenconditions.
-/
theorem mapParams {σ κ κ' : Type}
    (f : κ → κ')
    {Γ : List (FormulaH σ κ)} {φ : FormulaH σ κ} :
    Derives (σ := σ) (κ := κ) Γ φ →
      Derives (σ := σ) (κ := κ')
        (mapParamsContext (σ := σ) f Γ)
        (Syntax.Henkin.mapParamsFormula (σ := σ) f φ) := by
  intro h
  induction h with
  | hyp hmem =>
      refine Derives.hyp ?_
      exact List.mem_map.2 ⟨_, hmem, rfl⟩
  | topI =>
      exact Derives.topI
  | botE h ih =>
      exact Derives.botE ih
  | andI hφ hψ ihφ ihψ =>
      exact Derives.andI ihφ ihψ
  | andEL h ih =>
      exact Derives.andEL ih
  | andER h ih =>
      exact Derives.andER ih
  | orIL h ih =>
      exact Derives.orIL ih
  | orIR h ih =>
      exact Derives.orIR ih
  | orE hOr hL hR ihOr ihL ihR =>
      -- mapping distributes over `(::)` and preserves the disjunction shape.
      simpa [mapParamsContext, Syntax.Henkin.mapParamsFormula] using
        (Derives.orE ihOr ihL ihR)
  | impI h ih =>
      simpa [mapParamsContext, Syntax.Henkin.mapParamsFormula] using
        (Derives.impI ih)
  | impE hImp hArg ihImp ihArg =>
      exact Derives.impE ihImp ihArg
  | notI h ih =>
      simpa [mapParamsContext, Syntax.Henkin.mapParamsFormula] using
        (Derives.notI ih)
  | notE hNot hArg ihNot ihArg =>
      exact Derives.notE ihNot ihArg
  | piI haΓ haVars hInst ihInst =>
      rename_i Γ x a φ
      have haΓ' : a ∉ fvContext (σ := σ) (κ := κ') (mapParamsContext (σ := σ) f Γ) := by
        simpa [fvContext_mapParamsContext] using haΓ
      have haVars' :
          a ∉ Syntax.Henkin.varsFormula (σ := σ) (κ := κ')
            (Syntax.Henkin.mapParamsFormula (σ := σ) f φ) := by
        simpa [Syntax.Henkin.varsFormula_mapParamsFormula] using haVars
      have hInst' :
          Derives (σ := σ) (κ := κ')
            (mapParamsContext (σ := σ) f Γ)
            (Syntax.Henkin.substFormula (σ := σ) (κ := κ') x (.var a)
              (Syntax.Henkin.mapParamsFormula (σ := σ) f φ)) := by
        -- rewrite the IH goal using commutation of `mapParamsFormula` with substitution.
        simpa [Syntax.Henkin.mapParamsFormula_substFormula] using ihInst
      exact Derives.piI haΓ' haVars' hInst'
  | piE hPi ihPi =>
      rename_i Γ x t φ
      -- `mapParamsFormula` commutes with substitution, so the shape matches `piE`.
      simpa [Syntax.Henkin.mapParamsFormula_substFormula] using
        (Derives.piE (x := x) (t := Syntax.Henkin.mapParamsTerm f t) (φ := Syntax.Henkin.mapParamsFormula (σ := σ) f φ) ihPi)
  | sigmaI hInst ihInst =>
      rename_i Γ x t φ
      have hInst' :
          Derives (σ := σ) (κ := κ')
            (mapParamsContext (σ := σ) f Γ)
            (Syntax.Henkin.substFormula (σ := σ) (κ := κ') x (Syntax.Henkin.mapParamsTerm f t)
              (Syntax.Henkin.mapParamsFormula (σ := σ) f φ)) := by
        simpa [Syntax.Henkin.mapParamsFormula_substFormula] using ihInst
      exact Derives.sigmaI (x := x) (t := Syntax.Henkin.mapParamsTerm f t)
        (φ := Syntax.Henkin.mapParamsFormula (σ := σ) f φ) hInst'
  | sigmaE hSigma haΓ haVars haχ hHyp ihSigma ihHyp =>
      rename_i Γ x a φ χ
      have haΓ' : a ∉ fvContext (σ := σ) (κ := κ') (mapParamsContext (σ := σ) f Γ) := by
        simpa [fvContext_mapParamsContext] using haΓ
      have haVars' :
          a ∉ Syntax.Henkin.varsFormula (σ := σ) (κ := κ')
            (Syntax.Henkin.mapParamsFormula (σ := σ) f φ) := by
        simpa [Syntax.Henkin.varsFormula_mapParamsFormula] using haVars
      have haχ' :
          a ∉ Syntax.Henkin.fvFormula (σ := σ) (κ := κ')
            (Syntax.Henkin.mapParamsFormula (σ := σ) f χ) := by
        simpa [Syntax.Henkin.fvFormula_mapParamsFormula] using haχ
      have hHyp' :
          Derives (σ := σ) (κ := κ')
            (Syntax.Henkin.substFormula (σ := σ) (κ := κ') x (.var a)
              (Syntax.Henkin.mapParamsFormula (σ := σ) f φ) ::
              mapParamsContext (σ := σ) f Γ)
            (Syntax.Henkin.mapParamsFormula (σ := σ) f χ) := by
        -- `mapParamsContext` on `(t :: Γ)` is definitional, and substitution commutes.
        simpa [mapParamsContext, Syntax.Henkin.mapParamsFormula_substFormula] using ihHyp
      exact Derives.sigmaE ihSigma haΓ' haVars' haχ' hHyp'
  | wk hDer hSub ih =>
      rename_i Γ Δ φ
      have hSub' :
          mapParamsContext (σ := σ) f Γ ⊆ mapParamsContext (σ := σ) f Δ := by
        intro θ hθ
        rcases List.mem_map.1 hθ with ⟨ψ, hψ, rfl⟩
        exact List.mem_map.2 ⟨ψ, hSub hψ, rfl⟩
      exact Derives.wk ih hSub'

end Derives

/-- Lift a base-language context into the Henkin formula layer. -/
def liftContext {σ κ : Type} (Γ : List (Formula σ)) : List (FormulaH σ κ) :=
  Γ.map (Syntax.Henkin.liftFormula (σ := σ) (κ := κ))

@[simp] theorem fvContext_liftContext {σ κ : Type} (Γ : List (Formula σ)) :
    fvContext (σ := σ) (κ := κ) (liftContext (σ := σ) (κ := κ) Γ) =
      ND.fvContext (σ := σ) Γ := by
  induction Γ with
  | nil =>
      simp [liftContext, fvContext, ND.fvContext]
  | cons φ Γ ih =>
      simpa [liftContext, fvContext_cons, ND.fvContext_cons]
        using congrArg (fun s => Syntax.fvFormula (σ := σ) φ ∪ s) ih

theorem mem_liftContext_of_mem {σ κ : Type} {Γ : List (Formula σ)} {φ : Formula σ}
    (h : φ ∈ Γ) :
    Syntax.Henkin.liftFormula (σ := σ) (κ := κ) φ ∈ liftContext (σ := σ) (κ := κ) Γ := by
  exact List.mem_map.2 ⟨φ, h, rfl⟩

/--
Lift propositional ND derivations into Henkin ND derivations.

This provides an immediate bridge for existing quantifier-free developments.
-/
theorem derives_of_derivesProp_lift {σ κ : Type}
    {Γ : List (Formula σ)} {φ : Formula σ} :
    DerivesProp (σ := σ) Γ φ →
      Derives (σ := σ) (κ := κ)
        (liftContext (σ := σ) (κ := κ) Γ)
        (Syntax.Henkin.liftFormula (σ := σ) (κ := κ) φ) := by
  intro h
  induction h with
  | hyp hmem =>
      exact Derives.hyp (List.mem_map.2 ⟨_, hmem, rfl⟩)
  | topI =>
      exact Derives.topI
  | botE h ih =>
      exact Derives.botE ih
  | andI hφ hψ ihφ ihψ =>
      exact Derives.andI ihφ ihψ
  | andEL h ih =>
      exact Derives.andEL ih
  | andER h ih =>
      exact Derives.andER ih
  | orIL h ih =>
      exact Derives.orIL ih
  | orIR h ih =>
      exact Derives.orIR ih
  | orE hOr hφ hψ ihOr ihφ ihψ =>
      exact Derives.orE ihOr ihφ ihψ
  | impI h ih =>
      exact Derives.impI ih
  | impE hImp hArg ihImp ihArg =>
      exact Derives.impE ihImp ihArg
  | notI h ih =>
      exact Derives.notI ih
  | notE hNot hArg ihNot ihArg =>
      exact Derives.notE ihNot ihArg

/--
Lift full FO ND derivations into Henkin ND derivations.

Quantifier steps are preserved using the proven commutation between base substitution
and Henkin lifting for variable substitution.
-/
theorem derives_of_derives_lift {σ κ : Type}
    {Γ : List (Formula σ)} {φ : Formula σ} :
    HeytingLean.Noneism.Derives (σ := σ) Γ φ →
      Derives (σ := σ) (κ := κ)
        (liftContext (σ := σ) (κ := κ) Γ)
        (Syntax.Henkin.liftFormula (σ := σ) (κ := κ) φ) := by
  intro h
  induction h with
  | hyp hmem =>
      exact Derives.hyp (List.mem_map.2 ⟨_, hmem, rfl⟩)
  | topI =>
      exact Derives.topI
  | botE h ih =>
      exact Derives.botE ih
  | andI hφ hψ ihφ ihψ =>
      exact Derives.andI ihφ ihψ
  | andEL h ih =>
      exact Derives.andEL ih
  | andER h ih =>
      exact Derives.andER ih
  | orIL h ih =>
      exact Derives.orIL ih
  | orIR h ih =>
      exact Derives.orIR ih
  | orE hOr hφ hψ ihOr ihφ ihψ =>
      exact Derives.orE ihOr ihφ ihψ
  | impI h ih =>
      exact Derives.impI ih
  | impE hImp hArg ihImp ihArg =>
      exact Derives.impE ihImp ihArg
  | notI h ih =>
      exact Derives.notI ih
  | notE hNot hArg ihNot ihArg =>
      exact Derives.notE ihNot ihArg
  | piI haΓ haVars hInst ihInst =>
      rename_i Γ x a φ
      have haΓH : a ∉ fvContext (σ := σ) (κ := κ)
          (liftContext (σ := σ) (κ := κ) Γ) := by
        simpa [fvContext_liftContext] using haΓ
      have haVarsH : a ∉ Syntax.Henkin.varsFormula (σ := σ) (κ := κ)
          (Syntax.Henkin.liftFormula (σ := σ) (κ := κ) φ) := by
        simpa [Syntax.Henkin.varsFormula_liftFormula] using haVars
      have hInstH : Derives (σ := σ) (κ := κ)
          (liftContext (σ := σ) (κ := κ) Γ)
          (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x (.var a)
            (Syntax.Henkin.liftFormula (σ := σ) (κ := κ) φ)) := by
        simpa [Syntax.Henkin.liftFormula_substFormula_var (σ := σ) (κ := κ) x a φ] using ihInst
      exact Derives.piI haΓH haVarsH hInstH
  | piE hPi ihPi =>
      rename_i Γ x a φ
      have hInstH : Derives (σ := σ) (κ := κ)
          (liftContext (σ := σ) (κ := κ) Γ)
          (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x (.var a)
            (Syntax.Henkin.liftFormula (σ := σ) (κ := κ) φ)) :=
        Derives.piE ihPi
      simpa [Syntax.Henkin.liftFormula_substFormula_var (σ := σ) (κ := κ) x a φ] using hInstH
  | sigmaI hInst ihInst =>
      rename_i Γ x a φ
      have hInstH : Derives (σ := σ) (κ := κ)
          (liftContext (σ := σ) (κ := κ) Γ)
          (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x (.var a)
            (Syntax.Henkin.liftFormula (σ := σ) (κ := κ) φ)) := by
        simpa [Syntax.Henkin.liftFormula_substFormula_var (σ := σ) (κ := κ) x a φ] using ihInst
      exact Derives.sigmaI hInstH
  | sigmaE hSigma haΓ haVars haχ hHyp ihSigma ihHyp =>
      rename_i Γ x a φ χ
      have haΓH : a ∉ fvContext (σ := σ) (κ := κ)
          (liftContext (σ := σ) (κ := κ) Γ) := by
        simpa [fvContext_liftContext] using haΓ
      have haVarsH : a ∉ Syntax.Henkin.varsFormula (σ := σ) (κ := κ)
          (Syntax.Henkin.liftFormula (σ := σ) (κ := κ) φ) := by
        simpa [Syntax.Henkin.varsFormula_liftFormula] using haVars
      have haχH : a ∉ Syntax.Henkin.fvFormula (σ := σ) (κ := κ)
          (Syntax.Henkin.liftFormula (σ := σ) (κ := κ) χ) := by
        simpa [Syntax.Henkin.fvFormula_liftFormula] using haχ
      have hHypH : Derives (σ := σ) (κ := κ)
          (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x (.var a)
            (Syntax.Henkin.liftFormula (σ := σ) (κ := κ) φ) ::
              liftContext (σ := σ) (κ := κ) Γ)
          (Syntax.Henkin.liftFormula (σ := σ) (κ := κ) χ) := by
        simpa [liftContext, Syntax.Henkin.liftFormula_substFormula_var (σ := σ) (κ := κ) x a φ] using ihHyp
      exact Derives.sigmaE ihSigma haΓH haVarsH haχH hHypH
  | wk hDer hsub ih =>
      rename_i Γ Δ φ
      have hsubH :
          liftContext (σ := σ) (κ := κ) Γ ⊆ liftContext (σ := σ) (κ := κ) Δ := by
        intro θ hθ
        rcases List.mem_map.1 hθ with ⟨ψ, hψ, rfl⟩
        exact List.mem_map.2 ⟨ψ, hsub hψ, rfl⟩
      exact Derives.wk ih hsubH

end NDH
end Noneism
end HeytingLean
