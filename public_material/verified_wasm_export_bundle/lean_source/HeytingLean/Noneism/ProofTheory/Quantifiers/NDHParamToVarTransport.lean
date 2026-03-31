import HeytingLean.Noneism.ProofTheory.Quantifiers.NDHVarSupport
import HeytingLean.Noneism.Semantics.KripkeFOH

namespace HeytingLean
namespace Noneism
namespace NDH

open Syntax.Henkin

variable {σ κ : Type}

namespace Derives

/--
Transport a derivation through the param→var rewrite by supplying handlers for quantified rules.

This theorem isolates the remaining quantified obligations (`piI`, `piE`, `sigmaI`, `sigmaE`)
while fully discharging all structural/propositional constructors.
-/
theorem replaceParamWithVar_by_handlers
    [DecidableEq κ]
    (k : κ) (a : Var)
    {Γ : List (FormulaH σ κ)} {φ : FormulaH σ κ}
    (h : Derives (σ := σ) (κ := κ) Γ φ)
    (hPiI :
      ∀ {Δ : List (FormulaH σ κ)} {x b : Var} {ψ : FormulaH σ κ},
        b ∉ fvContext (σ := σ) (κ := κ) Δ →
        b ∉ varsFormula (σ := σ) (κ := κ) ψ →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.var b) ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi x ψ)))
    (hPiE :
      ∀ {Δ : List (FormulaH σ κ)} {x : Var} {t : TermH κ} {ψ : FormulaH σ κ},
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi x ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x t ψ)))
    (hSigmaI :
      ∀ {Δ : List (FormulaH σ κ)} {x : Var} {t : TermH κ} {ψ : FormulaH σ κ},
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x t ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma x ψ)))
    (hSigmaE :
      ∀ {Δ : List (FormulaH σ κ)} {x b : Var} {ψ χ : FormulaH σ κ},
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma x ψ)) →
        b ∉ fvContext (σ := σ) (κ := κ) Δ →
        b ∉ varsFormula (σ := σ) (κ := κ) ψ →
        b ∉ fvFormula (σ := σ) (κ := κ) χ →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.var b) ψ :: Δ))
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a χ) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a χ)) :
    Derives (σ := σ) (κ := κ)
      (replaceParamWithVarContext (σ := σ) (κ := κ) k a Γ)
      (replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ) := by
  induction h with
  | hyp hmem =>
      refine Derives.hyp ?_
      exact List.mem_map.2 ⟨_, hmem, rfl⟩
  | topI =>
      exact Derives.topI
  | botE hBot ihBot =>
      exact Derives.botE ihBot
  | andI hφ hψ ihφ ihψ =>
      exact Derives.andI ihφ ihψ
  | andEL hAnd ihAnd =>
      exact Derives.andEL ihAnd
  | andER hAnd ihAnd =>
      exact Derives.andER ihAnd
  | orIL hφ ihφ =>
      exact Derives.orIL ihφ
  | orIR hψ ihψ =>
      exact Derives.orIR ihψ
  | orE hOr hL hR ihOr ihL ihR =>
      simpa [replaceParamWithVarContext, replaceParamWithVarFormula] using
        (Derives.orE ihOr ihL ihR)
  | impI hImp ihImp =>
      simpa [replaceParamWithVarContext, replaceParamWithVarFormula] using
        (Derives.impI ihImp)
  | impE hImp hArg ihImp ihArg =>
      exact Derives.impE ihImp ihArg
  | notI hBot ihBot =>
      simpa [replaceParamWithVarContext, replaceParamWithVarFormula] using
        (Derives.notI ihBot)
  | notE hNot hArg ihNot ihArg =>
      exact Derives.notE ihNot ihArg
  | piI haΓ haVars hInst ihInst =>
      rename_i Δ x b ψ
      exact hPiI (Δ := Δ) (x := x) (b := b) (ψ := ψ) haΓ haVars ihInst
  | piE hPi ihPi =>
      rename_i Δ x t ψ
      exact hPiE (Δ := Δ) (x := x) (t := t) (ψ := ψ) ihPi
  | sigmaI hInst ihInst =>
      rename_i Δ x t ψ
      exact hSigmaI (Δ := Δ) (x := x) (t := t) (ψ := ψ) ihInst
  | sigmaE hSigma haΓ haVars haχ hDer ihSigma ihDer =>
      rename_i Δ x b ψ χ
      exact hSigmaE (Δ := Δ) (x := x) (b := b) (ψ := ψ) (χ := χ)
        ihSigma haΓ haVars haχ ihDer
  | wk hDer hSub ih =>
      rename_i Γ0 Δ ψ
      have hSub' :
          replaceParamWithVarContext (σ := σ) (κ := κ) k a Γ0 ⊆
            replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ := by
        intro θ hθ
        rcases List.mem_map.1 hθ with ⟨ψ, hψ, rfl⟩
        exact List.mem_map.2 ⟨ψ, hSub hψ, rfl⟩
      exact Derives.wk ih hSub'

theorem piE_handler_replaceParamWithVar_param_eq
    [DecidableEq κ]
    (k : κ) (a x : Var)
    {Δ : List (FormulaH σ κ)} {ψ : FormulaH σ κ}
    (ha :
      a ∉ varsFormula (σ := σ) (κ := κ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ))
    (hPi :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi x ψ))) :
    Derives (σ := σ) (κ := κ)
      (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
      (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
        (substFormula (σ := σ) (κ := κ) x (.param k) ψ)) := by
  have hPi' :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (.pi x (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ)) := by
    simpa [replaceParamWithVarFormula] using hPi
  have hInst :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (substFormula (σ := σ) (κ := κ) x (.var a)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ)) :=
    Derives.piE (x := x) (t := .var a)
      (φ := replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) hPi'
  have hComm :
      replaceParamWithVarFormula (σ := σ) (κ := κ) k a
          (substFormula (σ := σ) (κ := κ) x (.param k) ψ) =
        substFormula (σ := σ) (κ := κ) x (.var a)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) :=
    replaceParamWithVarFormula_substFormula_param_comm_of_not_mem
      (σ := σ) (κ := κ) k a x ψ ha
  simpa [hComm] using hInst

theorem piE_handler_replaceParamWithVar_param_eq_bound
    [DecidableEq κ]
    (k : κ) (a x : Var)
    {Δ : List (FormulaH σ κ)} {ψ : FormulaH σ κ}
    (haBound :
      a ∉ boundVars (σ := σ) (κ := κ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ))
    (hPi :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi x ψ))) :
    Derives (σ := σ) (κ := κ)
      (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
      (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
        (substFormula (σ := σ) (κ := κ) x (.param k) ψ)) := by
  have hPi' :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (.pi x (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ)) := by
    simpa [replaceParamWithVarFormula] using hPi
  have hInst :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (substFormula (σ := σ) (κ := κ) x (.var a)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ)) :=
    Derives.piE (x := x) (t := .var a)
      (φ := replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) hPi'
  have hComm :
      replaceParamWithVarFormula (σ := σ) (κ := κ) k a
          (substFormula (σ := σ) (κ := κ) x (.param k) ψ) =
        substFormula (σ := σ) (κ := κ) x (.var a)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) :=
    replaceParamWithVarFormula_substFormula_param_comm_of_not_mem_boundVars
      (σ := σ) (κ := κ) k a x ψ haBound
  simpa [hComm] using hInst

theorem piE_handler_replaceParamWithVar_param_eq_bound_original
    [DecidableEq κ]
    (k : κ) (a x : Var)
    {Δ : List (FormulaH σ κ)} {ψ : FormulaH σ κ}
    (haBound : a ∉ boundVars (σ := σ) (κ := κ) ψ)
    (hPi :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi x ψ))) :
    Derives (σ := σ) (κ := κ)
      (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
      (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
        (substFormula (σ := σ) (κ := κ) x (.param k) ψ)) := by
  have haBoundMapped :
      a ∉ boundVars (σ := σ) (κ := κ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) := by
    simpa [boundVars_replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ] using haBound
  exact piE_handler_replaceParamWithVar_param_eq_bound
    (σ := σ) (κ := κ) (k := k) (a := a) (x := x)
    (Δ := Δ) (ψ := ψ) haBoundMapped hPi

theorem piE_handler_replaceParamWithVar_param_eq_xeq
    [DecidableEq κ]
    (k : κ) (a x : Var)
    {Δ : List (FormulaH σ κ)} {ψ : FormulaH σ κ}
    (hxa : x = a)
    (hPi :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi x ψ))) :
    Derives (σ := σ) (κ := κ)
      (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
      (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
        (substFormula (σ := σ) (κ := κ) x (.param k) ψ)) := by
  subst x
  have hPi' :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (.pi a (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ)) := by
    simpa [replaceParamWithVarFormula] using hPi
  have hInst :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (substFormula (σ := σ) (κ := κ) a (.var a)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ)) :=
    Derives.piE (x := a) (t := .var a)
      (φ := replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) hPi'
  have hEq :
      replaceParamWithVarFormula (σ := σ) (κ := κ) k a
          (substFormula (σ := σ) (κ := κ) a (.param k) ψ) =
        substFormula (σ := σ) (κ := κ) a (.var a)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) := by
    calc
      replaceParamWithVarFormula (σ := σ) (κ := κ) k a
          (substFormula (σ := σ) (κ := κ) a (.param k) ψ) =
        replaceParamWithVarFormula (σ := σ) (κ := κ) k a
          (substFormulaParamNoAlpha (σ := σ) (κ := κ) a k ψ) := by
            simp [substFormula_param_eq_noAlpha (σ := σ) (κ := κ) a k ψ]
      _ =
        substFormulaVarNoAlpha (σ := σ) (κ := κ) a a
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) := by
            simpa using replaceParamWithVarFormula_substFormulaParamNoAlpha_comm
              (σ := σ) (κ := κ) k a a ψ
      _ =
        substFormula (σ := σ) (κ := κ) a (.var a)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) := by
            symm
            exact substFormula_var_self_eq_noAlpha (σ := σ) (κ := κ) a
              (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ)
  simpa [hEq] using hInst

theorem piE_handler_replaceParamWithVar_param_eq_xnotfv
    [DecidableEq κ]
    (k : κ) (a x : Var)
    {Δ : List (FormulaH σ κ)} {ψ : FormulaH σ κ}
    (hxψ : x ∉ fvFormula (σ := σ) (κ := κ) ψ)
    (hxa : x ≠ a)
    (hPi :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi x ψ))) :
    Derives (σ := σ) (κ := κ)
      (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
      (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
        (substFormula (σ := σ) (κ := κ) x (.param k) ψ)) := by
  have hPi' :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (.pi x (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ)) := by
    simpa [replaceParamWithVarFormula] using hPi
  have hxMapped :
      x ∉ fvFormula (σ := σ) (κ := κ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) :=
    not_mem_fvFormula_replaceParamWithVarFormula_of_not_mem_and_ne
      (σ := σ) (κ := κ) (a := a) (b := x) (k := k) (φ := ψ) hxψ hxa
  have hInst :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (substFormula (σ := σ) (κ := κ) x (.var a)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ)) :=
    Derives.piE (x := x) (t := .var a)
      (φ := replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) hPi'
  have hNoSubMapped :
      substFormula (σ := σ) (κ := κ) x (.var a)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) =
        replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ :=
    substFormula_eq_of_not_mem_fvFormula
      (σ := σ) (κ := κ) x (.var a)
      (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) hxMapped
  have hNoSubOrig :
      substFormula (σ := σ) (κ := κ) x (.param k) ψ = ψ :=
    substFormula_eq_of_not_mem_fvFormula (σ := σ) (κ := κ) x (.param k) ψ hxψ
  simpa [hNoSubMapped, hNoSubOrig] using hInst

theorem piE_handler_replaceParamWithVar_param_ne
    [DecidableEq κ]
    (k k' : κ) (a x : Var)
    {Δ : List (FormulaH σ κ)} {ψ : FormulaH σ κ}
    (hk' : k' ≠ k)
    (hxa : x ≠ a)
    (hPi :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi x ψ))) :
    Derives (σ := σ) (κ := κ)
      (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
      (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
        (substFormula (σ := σ) (κ := κ) x (.param k') ψ)) := by
  have hPi' :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (.pi x (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ)) := by
    simpa [replaceParamWithVarFormula] using hPi
  have hInst :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (substFormula (σ := σ) (κ := κ) x (.param k')
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ)) :=
    Derives.piE (x := x) (t := .param k')
      (φ := replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) hPi'
  have hComm :
      replaceParamWithVarFormula (σ := σ) (κ := κ) k a
          (substFormula (σ := σ) (κ := κ) x (.param k') ψ) =
        substFormula (σ := σ) (κ := κ) x (.param k')
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) :=
    replaceParamWithVarFormula_substFormula_param_ne_comm
      (σ := σ) (κ := κ) k k' a x hk' hxa ψ
  simpa [hComm] using hInst

theorem piE_handler_replaceParamWithVar_param_ne_param_free
    [DecidableEq κ]
    (k k' : κ) (a x : Var)
    {Δ : List (FormulaH σ κ)} {ψ : FormulaH σ κ}
    (hk' : k' ≠ k)
    (hkψ : k ∉ paramsFormula (σ := σ) (κ := κ) ψ)
    (hPi :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi x ψ))) :
    Derives (σ := σ) (κ := κ)
      (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
      (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
        (substFormula (σ := σ) (κ := κ) x (.param k') ψ)) := by
  have hkPi : k ∉ paramsFormula (σ := σ) (κ := κ) (.pi x ψ) := by
    simpa [paramsFormula] using hkψ
  have hPi' :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (.pi x ψ) := by
    simpa [replaceParamWithVarFormula_eq_of_not_mem_paramsFormula
      (σ := σ) (κ := κ) k a (.pi x ψ) hkPi] using hPi
  have hInst :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (substFormula (σ := σ) (κ := κ) x (.param k') ψ) :=
    Derives.piE (x := x) (t := .param k') (φ := ψ) hPi'
  have hComm :
      replaceParamWithVarFormula (σ := σ) (κ := κ) k a
          (substFormula (σ := σ) (κ := κ) x (.param k') ψ) =
        substFormula (σ := σ) (κ := κ) x (.param k')
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) :=
    replaceParamWithVarFormula_substFormula_param_ne_comm_of_not_mem_params
      (σ := σ) (κ := κ) k k' a x ψ hk' hkψ
  have hEqψ :
      replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ = ψ :=
    replaceParamWithVarFormula_eq_of_not_mem_paramsFormula
      (σ := σ) (κ := κ) k a ψ hkψ
  simpa [hComm, hEqψ] using hInst

theorem piE_handler_replaceParamWithVar_var
    [DecidableEq κ]
    (k : κ) (a x b : Var)
    {Δ : List (FormulaH σ κ)} {ψ : FormulaH σ κ}
    (hb : b ∉ varsFormula (σ := σ) (κ := κ) ψ)
    (hba : b ≠ a)
    (hxa : x ≠ a)
    (hPi :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi x ψ))) :
    Derives (σ := σ) (κ := κ)
      (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
      (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
        (substFormula (σ := σ) (κ := κ) x (.var b) ψ)) := by
  have hPi' :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (.pi x (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ)) := by
    simpa [replaceParamWithVarFormula] using hPi
  have hInst :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (substFormula (σ := σ) (κ := κ) x (.var b)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ)) :=
    Derives.piE (x := x) (t := .var b)
      (φ := replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) hPi'
  have hComm :
      replaceParamWithVarFormula (σ := σ) (κ := κ) k a
          (substFormula (σ := σ) (κ := κ) x (.var b) ψ) =
        substFormula (σ := σ) (κ := κ) x (.var b)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) :=
    replaceParamWithVarFormula_substFormula_var_comm_of_not_mem_and_ne
      (σ := σ) (κ := κ) k a x b ψ hb hba hxa
  simpa [hComm] using hInst

theorem piE_handler_replaceParamWithVar_var_param_free
    [DecidableEq κ]
    (k : κ) (a x b : Var)
    {Δ : List (FormulaH σ κ)} {ψ : FormulaH σ κ}
    (hkψ : k ∉ paramsFormula (σ := σ) (κ := κ) ψ)
    (hPi :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi x ψ))) :
    Derives (σ := σ) (κ := κ)
      (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
      (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
        (substFormula (σ := σ) (κ := κ) x (.var b) ψ)) := by
  have hPi' :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (.pi x (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ)) := by
    simpa [replaceParamWithVarFormula] using hPi
  have hInst :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (substFormula (σ := σ) (κ := κ) x (.var b)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ)) :=
    Derives.piE (x := x) (t := .var b)
      (φ := replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) hPi'
  have hComm :
      replaceParamWithVarFormula (σ := σ) (κ := κ) k a
          (substFormula (σ := σ) (κ := κ) x (.var b) ψ) =
        substFormula (σ := σ) (κ := κ) x (.var b)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) :=
    replaceParamWithVarFormula_substFormula_var_comm_of_not_mem_params
      (σ := σ) (κ := κ) k a x b ψ hkψ
  simpa [hComm] using hInst

theorem piE_handler_replaceParamWithVar_param_eq_param_free
    [DecidableEq κ]
    (k : κ) (a x : Var)
    {Δ : List (FormulaH σ κ)} {ψ : FormulaH σ κ}
    (hkψ : k ∉ paramsFormula (σ := σ) (κ := κ) ψ)
    (haψ : a ∉ varsFormula (σ := σ) (κ := κ) ψ)
    (hPi :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi x ψ))) :
    Derives (σ := σ) (κ := κ)
      (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
      (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
        (substFormula (σ := σ) (κ := κ) x (.param k) ψ)) := by
  have hEq :
      replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ = ψ :=
    replaceParamWithVarFormula_eq_of_not_mem_paramsFormula
      (σ := σ) (κ := κ) k a ψ hkψ
  have ha :
      a ∉ varsFormula (σ := σ) (κ := κ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) := by
    simpa [hEq] using haψ
  exact piE_handler_replaceParamWithVar_param_eq
    (σ := σ) (κ := κ) (k := k) (a := a) (x := x) (Δ := Δ) (ψ := ψ)
    ha hPi

theorem sigmaI_handler_replaceParamWithVar_param_eq
    [DecidableEq κ]
    (k : κ) (a x : Var)
    {Δ : List (FormulaH σ κ)} {ψ : FormulaH σ κ}
    (ha :
      a ∉ varsFormula (σ := σ) (κ := κ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ))
    (hInst :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
          (substFormula (σ := σ) (κ := κ) x (.param k) ψ))) :
    Derives (σ := σ) (κ := κ)
      (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
      (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma x ψ)) := by
  have hComm :
      replaceParamWithVarFormula (σ := σ) (κ := κ) k a
          (substFormula (σ := σ) (κ := κ) x (.param k) ψ) =
        substFormula (σ := σ) (κ := κ) x (.var a)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) :=
    replaceParamWithVarFormula_substFormula_param_comm_of_not_mem
      (σ := σ) (κ := κ) k a x ψ ha
  have hInst' :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (substFormula (σ := σ) (κ := κ) x (.var a)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ)) := by
    simpa [hComm] using hInst
  have hSig :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (.sigma x (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ)) :=
    Derives.sigmaI (x := x) (t := .var a)
      (φ := replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) hInst'
  simpa [replaceParamWithVarFormula] using hSig

theorem sigmaI_handler_replaceParamWithVar_param_eq_bound
    [DecidableEq κ]
    (k : κ) (a x : Var)
    {Δ : List (FormulaH σ κ)} {ψ : FormulaH σ κ}
    (haBound :
      a ∉ boundVars (σ := σ) (κ := κ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ))
    (hInst :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
          (substFormula (σ := σ) (κ := κ) x (.param k) ψ))) :
    Derives (σ := σ) (κ := κ)
      (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
      (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma x ψ)) := by
  have hComm :
      replaceParamWithVarFormula (σ := σ) (κ := κ) k a
          (substFormula (σ := σ) (κ := κ) x (.param k) ψ) =
        substFormula (σ := σ) (κ := κ) x (.var a)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) :=
    replaceParamWithVarFormula_substFormula_param_comm_of_not_mem_boundVars
      (σ := σ) (κ := κ) k a x ψ haBound
  have hInst' :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (substFormula (σ := σ) (κ := κ) x (.var a)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ)) := by
    simpa [hComm] using hInst
  have hSig :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (.sigma x (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ)) :=
    Derives.sigmaI (x := x) (t := .var a)
      (φ := replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) hInst'
  simpa [replaceParamWithVarFormula] using hSig

theorem sigmaI_handler_replaceParamWithVar_param_eq_bound_original
    [DecidableEq κ]
    (k : κ) (a x : Var)
    {Δ : List (FormulaH σ κ)} {ψ : FormulaH σ κ}
    (haBound : a ∉ boundVars (σ := σ) (κ := κ) ψ)
    (hInst :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
          (substFormula (σ := σ) (κ := κ) x (.param k) ψ))) :
    Derives (σ := σ) (κ := κ)
      (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
      (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma x ψ)) := by
  have haBoundMapped :
      a ∉ boundVars (σ := σ) (κ := κ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) := by
    simpa [boundVars_replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ] using haBound
  exact sigmaI_handler_replaceParamWithVar_param_eq_bound
    (σ := σ) (κ := κ) (k := k) (a := a) (x := x)
    (Δ := Δ) (ψ := ψ) haBoundMapped hInst

theorem sigmaI_handler_replaceParamWithVar_param_eq_xeq
    [DecidableEq κ]
    (k : κ) (a x : Var)
    {Δ : List (FormulaH σ κ)} {ψ : FormulaH σ κ}
    (hxa : x = a)
    (hInst :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
          (substFormula (σ := σ) (κ := κ) x (.param k) ψ))) :
    Derives (σ := σ) (κ := κ)
      (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
      (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma x ψ)) := by
  subst x
  have hEq :
      replaceParamWithVarFormula (σ := σ) (κ := κ) k a
          (substFormula (σ := σ) (κ := κ) a (.param k) ψ) =
        substFormula (σ := σ) (κ := κ) a (.var a)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) := by
    calc
      replaceParamWithVarFormula (σ := σ) (κ := κ) k a
          (substFormula (σ := σ) (κ := κ) a (.param k) ψ) =
        replaceParamWithVarFormula (σ := σ) (κ := κ) k a
          (substFormulaParamNoAlpha (σ := σ) (κ := κ) a k ψ) := by
            simp [substFormula_param_eq_noAlpha (σ := σ) (κ := κ) a k ψ]
      _ =
        substFormulaVarNoAlpha (σ := σ) (κ := κ) a a
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) := by
            simpa using replaceParamWithVarFormula_substFormulaParamNoAlpha_comm
              (σ := σ) (κ := κ) k a a ψ
      _ =
        substFormula (σ := σ) (κ := κ) a (.var a)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) := by
            symm
            exact substFormula_var_self_eq_noAlpha (σ := σ) (κ := κ) a
              (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ)
  have hInst' :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (substFormula (σ := σ) (κ := κ) a (.var a)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ)) := by
    simpa [hEq] using hInst
  have hSig :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (.sigma a (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ)) :=
    Derives.sigmaI (x := a) (t := .var a)
      (φ := replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) hInst'
  simpa [replaceParamWithVarFormula] using hSig

theorem sigmaI_handler_replaceParamWithVar_param_eq_xnotfv
    [DecidableEq κ]
    (k : κ) (a x : Var)
    {Δ : List (FormulaH σ κ)} {ψ : FormulaH σ κ}
    (hxψ : x ∉ fvFormula (σ := σ) (κ := κ) ψ)
    (hxa : x ≠ a)
    (hInst :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
          (substFormula (σ := σ) (κ := κ) x (.param k) ψ))) :
    Derives (σ := σ) (κ := κ)
      (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
      (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma x ψ)) := by
  have hxMapped :
      x ∉ fvFormula (σ := σ) (κ := κ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) :=
    not_mem_fvFormula_replaceParamWithVarFormula_of_not_mem_and_ne
      (σ := σ) (κ := κ) (a := a) (b := x) (k := k) (φ := ψ) hxψ hxa
  have hNoSubOrig :
      substFormula (σ := σ) (κ := κ) x (.param k) ψ = ψ :=
    substFormula_eq_of_not_mem_fvFormula (σ := σ) (κ := κ) x (.param k) ψ hxψ
  have hNoSubMapped :
      substFormula (σ := σ) (κ := κ) x (.var a)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) =
        replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ :=
    substFormula_eq_of_not_mem_fvFormula
      (σ := σ) (κ := κ) x (.var a)
      (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) hxMapped
  have hInstNoSub :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) := by
    simpa [hNoSubOrig] using hInst
  have hInstVar :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (substFormula (σ := σ) (κ := κ) x (.var a)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ)) := by
    simpa [hNoSubMapped] using hInstNoSub
  have hSig :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (.sigma x (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ)) :=
    Derives.sigmaI (x := x) (t := .var a)
      (φ := replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) hInstVar
  simpa [replaceParamWithVarFormula] using hSig

theorem sigmaI_handler_replaceParamWithVar_param_ne
    [DecidableEq κ]
    (k k' : κ) (a x : Var)
    {Δ : List (FormulaH σ κ)} {ψ : FormulaH σ κ}
    (hk' : k' ≠ k)
    (hxa : x ≠ a)
    (hInst :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
          (substFormula (σ := σ) (κ := κ) x (.param k') ψ))) :
    Derives (σ := σ) (κ := κ)
      (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
      (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma x ψ)) := by
  have hComm :
      replaceParamWithVarFormula (σ := σ) (κ := κ) k a
          (substFormula (σ := σ) (κ := κ) x (.param k') ψ) =
        substFormula (σ := σ) (κ := κ) x (.param k')
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) :=
    replaceParamWithVarFormula_substFormula_param_ne_comm
      (σ := σ) (κ := κ) k k' a x hk' hxa ψ
  have hInst' :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (substFormula (σ := σ) (κ := κ) x (.param k')
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ)) := by
    simpa [hComm] using hInst
  have hSig :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (.sigma x (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ)) :=
    Derives.sigmaI (x := x) (t := .param k')
      (φ := replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) hInst'
  simpa [replaceParamWithVarFormula] using hSig

theorem sigmaI_handler_replaceParamWithVar_param_ne_param_free
    [DecidableEq κ]
    (k k' : κ) (a x : Var)
    {Δ : List (FormulaH σ κ)} {ψ : FormulaH σ κ}
    (hk' : k' ≠ k)
    (hkψ : k ∉ paramsFormula (σ := σ) (κ := κ) ψ)
    (hInst :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
          (substFormula (σ := σ) (κ := κ) x (.param k') ψ))) :
    Derives (σ := σ) (κ := κ)
      (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
      (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma x ψ)) := by
  have hComm :
      replaceParamWithVarFormula (σ := σ) (κ := κ) k a
          (substFormula (σ := σ) (κ := κ) x (.param k') ψ) =
        substFormula (σ := σ) (κ := κ) x (.param k')
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) :=
    replaceParamWithVarFormula_substFormula_param_ne_comm_of_not_mem_params
      (σ := σ) (κ := κ) k k' a x ψ hk' hkψ
  have hEqψ :
      replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ = ψ :=
    replaceParamWithVarFormula_eq_of_not_mem_paramsFormula
      (σ := σ) (κ := κ) k a ψ hkψ
  have hInst' :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (substFormula (σ := σ) (κ := κ) x (.param k') ψ) := by
    simpa [hComm, hEqψ] using hInst
  have hSig :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (.sigma x ψ) :=
    Derives.sigmaI (x := x) (t := .param k') (φ := ψ) hInst'
  have hkSigma : k ∉ paramsFormula (σ := σ) (κ := κ) (.sigma x ψ) := by
    simpa [paramsFormula] using hkψ
  simpa [replaceParamWithVarFormula_eq_of_not_mem_paramsFormula
    (σ := σ) (κ := κ) k a (.sigma x ψ) hkSigma] using hSig

theorem sigmaI_handler_replaceParamWithVar_var
    [DecidableEq κ]
    (k : κ) (a x b : Var)
    {Δ : List (FormulaH σ κ)} {ψ : FormulaH σ κ}
    (hb : b ∉ varsFormula (σ := σ) (κ := κ) ψ)
    (hba : b ≠ a)
    (hxa : x ≠ a)
    (hInst :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
          (substFormula (σ := σ) (κ := κ) x (.var b) ψ))) :
    Derives (σ := σ) (κ := κ)
      (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
      (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma x ψ)) := by
  have hComm :
      replaceParamWithVarFormula (σ := σ) (κ := κ) k a
          (substFormula (σ := σ) (κ := κ) x (.var b) ψ) =
        substFormula (σ := σ) (κ := κ) x (.var b)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) :=
    replaceParamWithVarFormula_substFormula_var_comm_of_not_mem_and_ne
      (σ := σ) (κ := κ) k a x b ψ hb hba hxa
  have hInst' :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (substFormula (σ := σ) (κ := κ) x (.var b)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ)) := by
    simpa [hComm] using hInst
  have hSig :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (.sigma x (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ)) :=
    Derives.sigmaI (x := x) (t := .var b)
      (φ := replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) hInst'
  simpa [replaceParamWithVarFormula] using hSig

theorem sigmaI_handler_replaceParamWithVar_var_param_free
    [DecidableEq κ]
    (k : κ) (a x b : Var)
    {Δ : List (FormulaH σ κ)} {ψ : FormulaH σ κ}
    (hkψ : k ∉ paramsFormula (σ := σ) (κ := κ) ψ)
    (hInst :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
          (substFormula (σ := σ) (κ := κ) x (.var b) ψ))) :
    Derives (σ := σ) (κ := κ)
      (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
      (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma x ψ)) := by
  have hComm :
      replaceParamWithVarFormula (σ := σ) (κ := κ) k a
          (substFormula (σ := σ) (κ := κ) x (.var b) ψ) =
        substFormula (σ := σ) (κ := κ) x (.var b)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) :=
    replaceParamWithVarFormula_substFormula_var_comm_of_not_mem_params
      (σ := σ) (κ := κ) k a x b ψ hkψ
  have hInst' :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (substFormula (σ := σ) (κ := κ) x (.var b)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ)) := by
    simpa [hComm] using hInst
  have hSig :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (.sigma x (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ)) :=
    Derives.sigmaI (x := x) (t := .var b)
      (φ := replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) hInst'
  simpa [replaceParamWithVarFormula] using hSig

theorem sigmaI_handler_replaceParamWithVar_param_eq_param_free
    [DecidableEq κ]
    (k : κ) (a x : Var)
    {Δ : List (FormulaH σ κ)} {ψ : FormulaH σ κ}
    (hkψ : k ∉ paramsFormula (σ := σ) (κ := κ) ψ)
    (haψ : a ∉ varsFormula (σ := σ) (κ := κ) ψ)
    (hInst :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
          (substFormula (σ := σ) (κ := κ) x (.param k) ψ))) :
    Derives (σ := σ) (κ := κ)
      (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
      (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma x ψ)) := by
  have hEq :
      replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ = ψ :=
    replaceParamWithVarFormula_eq_of_not_mem_paramsFormula
      (σ := σ) (κ := κ) k a ψ hkψ
  have ha :
      a ∉ varsFormula (σ := σ) (κ := κ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) := by
    simpa [hEq] using haψ
  exact sigmaI_handler_replaceParamWithVar_param_eq
    (σ := σ) (κ := κ) (k := k) (a := a) (x := x) (Δ := Δ) (ψ := ψ)
    ha hInst

theorem piI_handler_replaceParamWithVar_var
    [DecidableEq κ]
    (k : κ) (a x b : Var)
    {Δ : List (FormulaH σ κ)} {ψ : FormulaH σ κ}
    (hbCtx : b ∉ fvContext (σ := σ) (κ := κ) Δ)
    (hbVars : b ∉ varsFormula (σ := σ) (κ := κ) ψ)
    (hba : b ≠ a)
    (hxa : x ≠ a)
    (hInst :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
          (substFormula (σ := σ) (κ := κ) x (.var b) ψ))) :
    Derives (σ := σ) (κ := κ)
      (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
      (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi x ψ)) := by
  have hbCtx' :
      b ∉ fvContext (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ) :=
    not_mem_fvContext_replaceParamWithVarContext_of_not_mem_fv_and_ne
      (σ := σ) (κ := κ) (a := a) (b := b) (k := k) (Γ := Δ) hbCtx hba
  have hbVars' :
      b ∉ varsFormula (σ := σ) (κ := κ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) :=
    not_mem_varsFormula_replaceParamWithVarFormula_of_not_mem_and_ne
      (σ := σ) (κ := κ) (a := a) (b := b) (k := k) (φ := ψ) hbVars hba
  have hComm :
      replaceParamWithVarFormula (σ := σ) (κ := κ) k a
          (substFormula (σ := σ) (κ := κ) x (.var b) ψ) =
        substFormula (σ := σ) (κ := κ) x (.var b)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) :=
    replaceParamWithVarFormula_substFormula_var_comm_of_not_mem_and_ne
      (σ := σ) (κ := κ) k a x b ψ hbVars hba hxa
  have hInst' :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (substFormula (σ := σ) (κ := κ) x (.var b)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ)) := by
    simpa [hComm] using hInst
  have hPi :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (.pi x (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ)) :=
    Derives.piI hbCtx' hbVars' hInst'
  simpa [replaceParamWithVarFormula] using hPi

theorem sigmaE_handler_replaceParamWithVar_var
    [DecidableEq κ]
    (k : κ) (a x b : Var)
    {Δ : List (FormulaH σ κ)} {ψ χ : FormulaH σ κ}
    (hSigma :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma x ψ)))
    (hbCtx : b ∉ fvContext (σ := σ) (κ := κ) Δ)
    (hbVars : b ∉ varsFormula (σ := σ) (κ := κ) ψ)
    (hbχ : b ∉ fvFormula (σ := σ) (κ := κ) χ)
    (hba : b ≠ a)
    (hxa : x ≠ a)
    (hDer :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a
          (substFormula (σ := σ) (κ := κ) x (.var b) ψ :: Δ))
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a χ)) :
    Derives (σ := σ) (κ := κ)
      (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
      (replaceParamWithVarFormula (σ := σ) (κ := κ) k a χ) := by
  have hSigma' :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (.sigma x (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ)) := by
    simpa [replaceParamWithVarFormula] using hSigma
  have hbCtx' :
      b ∉ fvContext (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ) :=
    not_mem_fvContext_replaceParamWithVarContext_of_not_mem_fv_and_ne
      (σ := σ) (κ := κ) (a := a) (b := b) (k := k) (Γ := Δ) hbCtx hba
  have hbVars' :
      b ∉ varsFormula (σ := σ) (κ := κ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) :=
    not_mem_varsFormula_replaceParamWithVarFormula_of_not_mem_and_ne
      (σ := σ) (κ := κ) (a := a) (b := b) (k := k) (φ := ψ) hbVars hba
  have hbχ' :
      b ∉ fvFormula (σ := σ) (κ := κ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a χ) :=
    not_mem_fvFormula_replaceParamWithVarFormula_of_not_mem_and_ne
      (σ := σ) (κ := κ) (a := a) (b := b) (k := k) (φ := χ) hbχ hba
  have hComm :
      replaceParamWithVarFormula (σ := σ) (κ := κ) k a
          (substFormula (σ := σ) (κ := κ) x (.var b) ψ) =
        substFormula (σ := σ) (κ := κ) x (.var b)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) :=
    replaceParamWithVarFormula_substFormula_var_comm_of_not_mem_and_ne
      (σ := σ) (κ := κ) k a x b ψ hbVars hba hxa
  have hDer' :
      Derives (σ := σ) (κ := κ)
        (substFormula (σ := σ) (κ := κ) x (.var b)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ) ::
          replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a χ) := by
    simpa [replaceParamWithVarContext, hComm] using hDer
  exact Derives.sigmaE hSigma' hbCtx' hbVars' hbχ' hDer'

/--
Freshness-packaged `piI` transport: pick an admissible fresh variable automatically,
then discharge `piI` via `piI_handler_replaceParamWithVar_var`.
-/
theorem piI_handler_replaceParamWithVar_var_fresh
    [DecidableEq κ]
    (k : κ) (a x : Var)
    {Δ : List (FormulaH σ κ)} {ψ : FormulaH σ κ}
    (hxa : x ≠ a)
    (hInstFresh :
      ∀ b : Var,
        b ≠ a →
        b ≠ x →
        b ∉ fvContext (σ := σ) (κ := κ) Δ →
        b ∉ varsFormula (σ := σ) (κ := κ) ψ →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.var b) ψ))) :
    Derives (σ := σ) (κ := κ)
      (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
      (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi x ψ)) := by
  rcases exists_fresh_for_sigma_side_conditions_and_ne
      (σ := σ) (κ := κ) Δ ψ ψ a x with
    ⟨b, hba, hbx, hbCtx, hbVars, _hbψ⟩
  exact piI_handler_replaceParamWithVar_var
    (σ := σ) (κ := κ) (k := k) (a := a) (x := x) (b := b)
    hbCtx hbVars hba hxa
    (hInstFresh b hba hbx hbCtx hbVars)

/--
Freshness-packaged `sigmaE` transport: pick an admissible fresh variable automatically,
then discharge `sigmaE` via `sigmaE_handler_replaceParamWithVar_var`.
-/
theorem sigmaE_handler_replaceParamWithVar_var_fresh
    [DecidableEq κ]
    (k : κ) (a x : Var)
    {Δ : List (FormulaH σ κ)} {ψ χ : FormulaH σ κ}
    (hxa : x ≠ a)
    (hSigma :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma x ψ)))
    (hDerFresh :
      ∀ b : Var,
        b ≠ a →
        b ≠ x →
        b ∉ fvContext (σ := σ) (κ := κ) Δ →
        b ∉ varsFormula (σ := σ) (κ := κ) ψ →
        b ∉ fvFormula (σ := σ) (κ := κ) χ →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.var b) ψ :: Δ))
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a χ)) :
    Derives (σ := σ) (κ := κ)
      (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
      (replaceParamWithVarFormula (σ := σ) (κ := κ) k a χ) := by
  rcases exists_fresh_for_sigma_side_conditions_and_ne
      (σ := σ) (κ := κ) Δ ψ χ a x with
    ⟨b, hba, hbx, hbCtx, hbVars, hbχ⟩
  exact sigmaE_handler_replaceParamWithVar_var
    (σ := σ) (κ := κ) (k := k) (a := a) (x := x) (b := b)
    hSigma hbCtx hbVars hbχ hba hxa
    (hDerFresh b hba hbx hbCtx hbVars hbχ)

/--
Reduction wrapper for handler-instantiation:
`piE`/`sigmaI` variable-instantiation obligations are automatically discharged when
the distinguished parameter `k` is absent from the quantified body (`k ∉ paramsFormula ψ`).

What remains to be supplied explicitly are the `k`-present variable-instantiation branches
and the parameter-instantiation branches.
-/
theorem replaceParamWithVar_by_handlers_reduce_to_kpresent_var
    [DecidableEq κ]
    (k : κ) (a : Var)
    {Γ : List (FormulaH σ κ)} {φ : FormulaH σ κ}
    (h : Derives (σ := σ) (κ := κ) Γ φ)
    (hPiI :
      ∀ {Δ : List (FormulaH σ κ)} {x b : Var} {ψ : FormulaH σ κ},
        b ∉ fvContext (σ := σ) (κ := κ) Δ →
        b ∉ varsFormula (σ := σ) (κ := κ) ψ →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.var b) ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi x ψ)))
    (hPiE_param_eq :
      ∀ {Δ : List (FormulaH σ κ)} {x : Var} {ψ : FormulaH σ κ},
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi x ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.param k) ψ)))
    (hPiE_param_ne :
      ∀ {Δ : List (FormulaH σ κ)} {x : Var} {k' : κ} {ψ : FormulaH σ κ},
        k' ≠ k →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi x ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.param k') ψ)))
    (hPiE_var_kpresent :
      ∀ {Δ : List (FormulaH σ κ)} {x b : Var} {ψ : FormulaH σ κ},
        k ∈ paramsFormula (σ := σ) (κ := κ) ψ →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi x ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.var b) ψ)))
    (hSigmaI_param_eq :
      ∀ {Δ : List (FormulaH σ κ)} {x : Var} {ψ : FormulaH σ κ},
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.param k) ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma x ψ)))
    (hSigmaI_param_ne :
      ∀ {Δ : List (FormulaH σ κ)} {x : Var} {k' : κ} {ψ : FormulaH σ κ},
        k' ≠ k →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.param k') ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma x ψ)))
    (hSigmaI_var_kpresent :
      ∀ {Δ : List (FormulaH σ κ)} {x b : Var} {ψ : FormulaH σ κ},
        k ∈ paramsFormula (σ := σ) (κ := κ) ψ →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.var b) ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma x ψ)))
    (hSigmaE :
      ∀ {Δ : List (FormulaH σ κ)} {x b : Var} {ψ χ : FormulaH σ κ},
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma x ψ)) →
        b ∉ fvContext (σ := σ) (κ := κ) Δ →
        b ∉ varsFormula (σ := σ) (κ := κ) ψ →
        b ∉ fvFormula (σ := σ) (κ := κ) χ →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.var b) ψ :: Δ))
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a χ) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a χ)) :
    Derives (σ := σ) (κ := κ)
      (replaceParamWithVarContext (σ := σ) (κ := κ) k a Γ)
      (replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ) := by
  refine replaceParamWithVar_by_handlers
    (σ := σ) (κ := κ) (k := k) (a := a) (Γ := Γ) (φ := φ) h hPiI ?_ ?_ hSigmaE
  ·
    intro Δ x t ψ hPi
    cases t with
    | var b =>
        by_cases hkψ : k ∈ paramsFormula (σ := σ) (κ := κ) ψ
        · exact hPiE_var_kpresent (Δ := Δ) (x := x) (b := b) (ψ := ψ) hkψ hPi
        ·
          exact piE_handler_replaceParamWithVar_var_param_free
            (σ := σ) (κ := κ) (k := k) (a := a) (x := x) (b := b)
            (Δ := Δ) (ψ := ψ) (by simpa using hkψ) hPi
    | param k' =>
        by_cases hk' : k' = k
        · subst hk'
          exact hPiE_param_eq (Δ := Δ) (x := x) (ψ := ψ) hPi
        · exact hPiE_param_ne (Δ := Δ) (x := x) (k' := k') (ψ := ψ) hk' hPi
  ·
    intro Δ x t ψ hInst
    cases t with
    | var b =>
        by_cases hkψ : k ∈ paramsFormula (σ := σ) (κ := κ) ψ
        · exact hSigmaI_var_kpresent (Δ := Δ) (x := x) (b := b) (ψ := ψ) hkψ hInst
        ·
          exact sigmaI_handler_replaceParamWithVar_var_param_free
            (σ := σ) (κ := κ) (k := k) (a := a) (x := x) (b := b)
            (Δ := Δ) (ψ := ψ) (by simpa using hkψ) hInst
    | param k' =>
        by_cases hk' : k' = k
        · subst hk'
          exact hSigmaI_param_eq (Δ := Δ) (x := x) (ψ := ψ) hInst
        · exact hSigmaI_param_ne (Δ := Δ) (x := x) (k' := k') (ψ := ψ) hk' hInst

theorem replaceParamWithVar_by_handlers_reduce_to_kpresent_plus_xeq
    [DecidableEq κ]
    (k : κ) (a : Var)
    {Γ : List (FormulaH σ κ)} {φ : FormulaH σ κ}
    (h : Derives (σ := σ) (κ := κ) Γ φ)
    (hFreshKfree :
      ∀ {ψ : FormulaH σ κ},
        k ∉ paramsFormula (σ := σ) (κ := κ) ψ →
        a ∉ varsFormula (σ := σ) (κ := κ) ψ)
    (hPiI :
      ∀ {Δ : List (FormulaH σ κ)} {x b : Var} {ψ : FormulaH σ κ},
        b ∉ fvContext (σ := σ) (κ := κ) Δ →
        b ∉ varsFormula (σ := σ) (κ := κ) ψ →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.var b) ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi x ψ)))
    (hPiE_param_eq_kpresent :
      ∀ {Δ : List (FormulaH σ κ)} {x : Var} {ψ : FormulaH σ κ},
        k ∈ paramsFormula (σ := σ) (κ := κ) ψ →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi x ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.param k) ψ)))
    (hPiE_param_ne_xeq :
      ∀ {Δ : List (FormulaH σ κ)} {x : Var} {k' : κ} {ψ : FormulaH σ κ},
        k' ≠ k →
        x = a →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi x ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.param k') ψ)))
    (hPiE_var_kpresent :
      ∀ {Δ : List (FormulaH σ κ)} {x b : Var} {ψ : FormulaH σ κ},
        k ∈ paramsFormula (σ := σ) (κ := κ) ψ →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi x ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.var b) ψ)))
    (hSigmaI_param_eq_kpresent :
      ∀ {Δ : List (FormulaH σ κ)} {x : Var} {ψ : FormulaH σ κ},
        k ∈ paramsFormula (σ := σ) (κ := κ) ψ →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.param k) ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma x ψ)))
    (hSigmaI_param_ne_xeq :
      ∀ {Δ : List (FormulaH σ κ)} {x : Var} {k' : κ} {ψ : FormulaH σ κ},
        k' ≠ k →
        x = a →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.param k') ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma x ψ)))
    (hSigmaI_var_kpresent :
      ∀ {Δ : List (FormulaH σ κ)} {x b : Var} {ψ : FormulaH σ κ},
        k ∈ paramsFormula (σ := σ) (κ := κ) ψ →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.var b) ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma x ψ)))
    (hSigmaE :
      ∀ {Δ : List (FormulaH σ κ)} {x b : Var} {ψ χ : FormulaH σ κ},
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma x ψ)) →
        b ∉ fvContext (σ := σ) (κ := κ) Δ →
        b ∉ varsFormula (σ := σ) (κ := κ) ψ →
        b ∉ fvFormula (σ := σ) (κ := κ) χ →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.var b) ψ :: Δ))
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a χ) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a χ)) :
    Derives (σ := σ) (κ := κ)
      (replaceParamWithVarContext (σ := σ) (κ := κ) k a Γ)
      (replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ) := by
  refine replaceParamWithVar_by_handlers_reduce_to_kpresent_var
    (σ := σ) (κ := κ) (k := k) (a := a) (Γ := Γ) (φ := φ) h
    hPiI ?_ ?_ hPiE_var_kpresent ?_ ?_ hSigmaI_var_kpresent hSigmaE
  ·
    intro Δ x ψ hPi
    by_cases hxfv : x ∈ fvFormula (σ := σ) (κ := κ) ψ
    ·
      by_cases hkψ : k ∈ paramsFormula (σ := σ) (κ := κ) ψ
      · exact hPiE_param_eq_kpresent (Δ := Δ) (x := x) (ψ := ψ) hkψ hPi
      ·
        exact piE_handler_replaceParamWithVar_param_eq_param_free
          (σ := σ) (κ := κ) (k := k) (a := a) (x := x) (Δ := Δ) (ψ := ψ)
          (by simpa using hkψ) (hFreshKfree (by simpa using hkψ)) hPi
    ·
      have hxψ : x ∉ fvFormula (σ := σ) (κ := κ) ψ := by
        simpa using hxfv
      by_cases hxa : x = a
      ·
        by_cases hkψ : k ∈ paramsFormula (σ := σ) (κ := κ) ψ
        · exact hPiE_param_eq_kpresent (Δ := Δ) (x := x) (ψ := ψ) hkψ hPi
        ·
          exact piE_handler_replaceParamWithVar_param_eq_param_free
            (σ := σ) (κ := κ) (k := k) (a := a) (x := x) (Δ := Δ) (ψ := ψ)
            (by simpa using hkψ) (hFreshKfree (by simpa using hkψ)) hPi
      ·
        exact piE_handler_replaceParamWithVar_param_eq_xnotfv
          (σ := σ) (κ := κ) (k := k) (a := a) (x := x)
          (Δ := Δ) (ψ := ψ) hxψ hxa hPi
  ·
    intro Δ x k' ψ hk' hPi
    by_cases hxa : x = a
    · exact hPiE_param_ne_xeq (Δ := Δ) (x := x) (k' := k') (ψ := ψ) hk' hxa hPi
    · exact piE_handler_replaceParamWithVar_param_ne
        (σ := σ) (κ := κ) (k := k) (k' := k') (a := a) (x := x)
        (Δ := Δ) (ψ := ψ) hk' hxa hPi
  ·
    intro Δ x ψ hInst
    by_cases hxfv : x ∈ fvFormula (σ := σ) (κ := κ) ψ
    ·
      by_cases hkψ : k ∈ paramsFormula (σ := σ) (κ := κ) ψ
      · exact hSigmaI_param_eq_kpresent (Δ := Δ) (x := x) (ψ := ψ) hkψ hInst
      ·
        exact sigmaI_handler_replaceParamWithVar_param_eq_param_free
          (σ := σ) (κ := κ) (k := k) (a := a) (x := x) (Δ := Δ) (ψ := ψ)
          (by simpa using hkψ) (hFreshKfree (by simpa using hkψ)) hInst
    ·
      have hxψ : x ∉ fvFormula (σ := σ) (κ := κ) ψ := by
        simpa using hxfv
      by_cases hxa : x = a
      ·
        by_cases hkψ : k ∈ paramsFormula (σ := σ) (κ := κ) ψ
        · exact hSigmaI_param_eq_kpresent (Δ := Δ) (x := x) (ψ := ψ) hkψ hInst
        ·
          exact sigmaI_handler_replaceParamWithVar_param_eq_param_free
            (σ := σ) (κ := κ) (k := k) (a := a) (x := x) (Δ := Δ) (ψ := ψ)
            (by simpa using hkψ) (hFreshKfree (by simpa using hkψ)) hInst
      ·
        exact sigmaI_handler_replaceParamWithVar_param_eq_xnotfv
          (σ := σ) (κ := κ) (k := k) (a := a) (x := x)
          (Δ := Δ) (ψ := ψ) hxψ hxa hInst
  ·
    intro Δ x k' ψ hk' hInst
    by_cases hxa : x = a
    · exact hSigmaI_param_ne_xeq (Δ := Δ) (x := x) (k' := k') (ψ := ψ) hk' hxa hInst
    · exact sigmaI_handler_replaceParamWithVar_param_ne
        (σ := σ) (κ := κ) (k := k) (k' := k') (a := a) (x := x)
        (Δ := Δ) (ψ := ψ) hk' hxa hInst

/--
Refined reduction wrapper:
all `k`-free parameter-instantiation branches (`k' ≠ k`) are discharged automatically,
including the `x = a` corner. Remaining explicit obligations are now restricted to
`k`-present branches.
-/
theorem replaceParamWithVar_by_handlers_reduce_to_kpresent_only
    [DecidableEq κ]
    (k : κ) (a : Var)
    {Γ : List (FormulaH σ κ)} {φ : FormulaH σ κ}
    (h : Derives (σ := σ) (κ := κ) Γ φ)
    (hFreshKfree :
      ∀ {ψ : FormulaH σ κ},
        k ∉ paramsFormula (σ := σ) (κ := κ) ψ →
        a ∉ varsFormula (σ := σ) (κ := κ) ψ)
    (hPiI :
      ∀ {Δ : List (FormulaH σ κ)} {x b : Var} {ψ : FormulaH σ κ},
        b ∉ fvContext (σ := σ) (κ := κ) Δ →
        b ∉ varsFormula (σ := σ) (κ := κ) ψ →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.var b) ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi x ψ)))
    (hPiE_param_eq_kpresent :
      ∀ {Δ : List (FormulaH σ κ)} {x : Var} {ψ : FormulaH σ κ},
        k ∈ paramsFormula (σ := σ) (κ := κ) ψ →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi x ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.param k) ψ)))
    (hPiE_param_ne_xeq_kpresent :
      ∀ {Δ : List (FormulaH σ κ)} {x : Var} {k' : κ} {ψ : FormulaH σ κ},
        k ∈ paramsFormula (σ := σ) (κ := κ) ψ →
        k' ≠ k →
        x = a →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi x ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.param k') ψ)))
    (hPiE_var_kpresent :
      ∀ {Δ : List (FormulaH σ κ)} {x b : Var} {ψ : FormulaH σ κ},
        k ∈ paramsFormula (σ := σ) (κ := κ) ψ →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi x ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.var b) ψ)))
    (hSigmaI_param_eq_kpresent :
      ∀ {Δ : List (FormulaH σ κ)} {x : Var} {ψ : FormulaH σ κ},
        k ∈ paramsFormula (σ := σ) (κ := κ) ψ →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.param k) ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma x ψ)))
    (hSigmaI_param_ne_xeq_kpresent :
      ∀ {Δ : List (FormulaH σ κ)} {x : Var} {k' : κ} {ψ : FormulaH σ κ},
        k ∈ paramsFormula (σ := σ) (κ := κ) ψ →
        k' ≠ k →
        x = a →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.param k') ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma x ψ)))
    (hSigmaI_var_kpresent :
      ∀ {Δ : List (FormulaH σ κ)} {x b : Var} {ψ : FormulaH σ κ},
        k ∈ paramsFormula (σ := σ) (κ := κ) ψ →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.var b) ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma x ψ)))
    (hSigmaE :
      ∀ {Δ : List (FormulaH σ κ)} {x b : Var} {ψ χ : FormulaH σ κ},
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma x ψ)) →
        b ∉ fvContext (σ := σ) (κ := κ) Δ →
        b ∉ varsFormula (σ := σ) (κ := κ) ψ →
        b ∉ fvFormula (σ := σ) (κ := κ) χ →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.var b) ψ :: Δ))
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a χ) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a χ)) :
    Derives (σ := σ) (κ := κ)
      (replaceParamWithVarContext (σ := σ) (κ := κ) k a Γ)
      (replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ) := by
  refine replaceParamWithVar_by_handlers_reduce_to_kpresent_plus_xeq
    (σ := σ) (κ := κ) (k := k) (a := a) (Γ := Γ) (φ := φ) h
    hFreshKfree hPiI hPiE_param_eq_kpresent ?_ hPiE_var_kpresent
    hSigmaI_param_eq_kpresent ?_ hSigmaI_var_kpresent hSigmaE
  ·
    intro Δ x k' ψ hk' hxa hPi
    by_cases hkψ : k ∈ paramsFormula (σ := σ) (κ := κ) ψ
    · exact hPiE_param_ne_xeq_kpresent
        (Δ := Δ) (x := x) (k' := k') (ψ := ψ) hkψ hk' hxa hPi
    ·
      exact piE_handler_replaceParamWithVar_param_ne_param_free
        (σ := σ) (κ := κ) (k := k) (k' := k') (a := a) (x := x)
        (Δ := Δ) (ψ := ψ) hk' (by simpa using hkψ) hPi
  ·
    intro Δ x k' ψ hk' hxa hInst
    by_cases hkψ : k ∈ paramsFormula (σ := σ) (κ := κ) ψ
    · exact hSigmaI_param_ne_xeq_kpresent
        (Δ := Δ) (x := x) (k' := k') (ψ := ψ) hkψ hk' hxa hInst
    ·
      exact sigmaI_handler_replaceParamWithVar_param_ne_param_free
        (σ := σ) (κ := κ) (k := k) (k' := k') (a := a) (x := x)
        (Δ := Δ) (ψ := ψ) hk' (by simpa using hkψ) hInst

/-
Core-frontier reduction wrapper.

Compared to `...reduce_to_kpresent_only`, this narrows the explicit `k`-present
`param = k` obligations to the alpha-sensitive shape:
- `x ∈ fvFormula ψ` and `a ∈ boundVars ψ`.

The `x = a` branch is discharged automatically via
`piE_handler_replaceParamWithVar_param_eq_xeq` and
`sigmaI_handler_replaceParamWithVar_param_eq_xeq`.
The complementary branch (`x ≠ a` and `x ∉ fvFormula ψ`) is discharged automatically
via `piE_handler_replaceParamWithVar_param_eq_xnotfv` and
`sigmaI_handler_replaceParamWithVar_param_eq_xnotfv`.
For `x ∈ fvFormula ψ` with `x ≠ a`, the non-conflict case `a ∉ boundVars ψ` is also
discharged automatically via bound-vars commutation handlers.
-/
/--
Concrete inhabitant of the residual core-conflict quadrant.

This witnesses that the branch conditions are not vacuous.
-/
theorem kpresent_core_conflict_quadrant_witness :
    let ψ : FormulaH PUnit Nat := .sigma 0 (.pred () [.var 1, .param 0])
    let k : Nat := 0
    let a : Var := 0
    let x : Var := 1
    k ∈ paramsFormula (σ := PUnit) (κ := Nat) ψ ∧
      x ∈ fvFormula (σ := PUnit) (κ := Nat) ψ ∧
      a ∈ boundVars (σ := PUnit) (κ := Nat) ψ ∧
      x ≠ a := by
  native_decide

/--
Concrete mismatch at the exact `k`-present transport shape used by the core-conflict branch.

This shows the target formula cannot be obtained by a pure commutation/equality rewrite from
`piE`/`sigmaI` with witness term `(.var a)` in the conflict quadrant.
-/
theorem kpresent_core_conflict_formula_mismatch :
    let ψ : FormulaH PUnit Nat := .sigma 0 (.pred () [.var 1, .param 0])
    let k : Nat := 0
    let a : Var := 0
    let x : Var := 1
    replaceParamWithVarFormula (σ := PUnit) (κ := Nat) k a
        (substFormula (σ := PUnit) (κ := Nat) x (.param k) ψ) ≠
      substFormula (σ := PUnit) (κ := Nat) x (.var a)
        (replaceParamWithVarFormula (σ := PUnit) (κ := Nat) k a ψ) := by
  native_decide

/--
Semantic counterexample at the exact core-conflict shape.

For `ψ := ∀ a, P(x,a)` with `P` interpreted as equality on `Bool`, the transported
`param = k` premise becomes `∀ a, P(a,a)` (true), while the sigma target is
`∃ x, ∀ a, P(x,a)` (false). This shows the remaining sigma-side conflict bridge
cannot be discharged by a purely syntactic commutation argument.
-/
theorem kpresent_core_conflict_sigmaI_semantic_counterexample :
    let ψ : FormulaH PUnit Nat := .pi 0 (.pred () [.var 1, .param 0])
    let k : Nat := 0
    let a : Var := 0
    let x : Var := 1
    let M : HeytingLean.Noneism.KripkeFOH.Model Unit PUnit Bool := {
      valPred := fun _ _ args =>
        match args with
        | [u, v] => u = v
        | _ => False
      monoPred := by
        intro _ _ _ _ _ h
        exact h
      valEx := fun _ _ => True
      monoEx := by
        intro _ _ _ _ h
        exact h
    }
    let ρ : HeytingLean.Noneism.KripkeFOH.Valuation Bool := fun _ => false
    let η : HeytingLean.Noneism.KripkeFOH.ParamInterp Nat Bool := fun _ => false
    HeytingLean.Noneism.KripkeFOH.Forces M ρ η ()
      (replaceParamWithVarFormula (σ := PUnit) (κ := Nat) k a
        (substFormula (σ := PUnit) (κ := Nat) x (.param k) ψ)) ∧
    ¬ HeytingLean.Noneism.KripkeFOH.Forces M ρ η ()
      (.sigma x (replaceParamWithVarFormula (σ := PUnit) (κ := Nat) k a ψ)) := by
  simp [HeytingLean.Noneism.KripkeFOH.Forces,
    replaceParamWithVarFormula, replaceParamWithVarTerms, replaceParamWithVarTerm,
    substFormula, substTerm, substTerms]
  native_decide

class HasParamEqKpresentCoreConflictHandlers (σ : Type) (κ : Type) [DecidableEq κ] : Prop where
  piE_param_eq_kpresent_core_conflict :
    ∀ (k : κ) (a : Var)
      {Δ : List (FormulaH σ κ)} {x : Var} {ψ : FormulaH σ κ},
      k ∈ paramsFormula (σ := σ) (κ := κ) ψ →
      x ∈ fvFormula (σ := σ) (κ := κ) ψ →
      a ∈ boundVars (σ := σ) (κ := κ) ψ →
      x ≠ a →
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi x ψ)) →
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
          (substFormula (σ := σ) (κ := κ) x (.param k) ψ))
  sigmaI_param_eq_kpresent_core_conflict :
    ∀ (k : κ) (a : Var)
      {Δ : List (FormulaH σ κ)} {x : Var} {ψ : FormulaH σ κ},
      k ∈ paramsFormula (σ := σ) (κ := κ) ψ →
      x ∈ fvFormula (σ := σ) (κ := κ) ψ →
      a ∈ boundVars (σ := σ) (κ := κ) ψ →
      x ≠ a →
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
          (substFormula (σ := σ) (κ := κ) x (.param k) ψ)) →
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma x ψ))

/--
Derivability bridge between capture-avoiding variable substitution and the
no-alpha substitution variant.

This bridge is intentionally freshness-scoped: without binder freshness, no-alpha
substitution can change binding structure and is not globally derivability-preserving.
-/
class HasSubstFormulaVarNoAlphaDerivableBridge
    (σ : Type) (κ : Type) [DecidableEq κ] : Prop where
  to_noAlpha :
    ∀ {Γ : List (FormulaH σ κ)} {x a : Var} {φ : FormulaH σ κ},
      a ∉ boundVars (σ := σ) (κ := κ) φ →
      Derives (σ := σ) (κ := κ) Γ
        (substFormula (σ := σ) (κ := κ) x (.var a) φ) →
      Derives (σ := σ) (κ := κ) Γ
        (substFormulaVarNoAlpha (σ := σ) (κ := κ) x a φ)
  of_noAlpha :
    ∀ {Γ : List (FormulaH σ κ)} {x a : Var} {φ : FormulaH σ κ},
      a ∉ boundVars (σ := σ) (κ := κ) φ →
      Derives (σ := σ) (κ := κ) Γ
        (substFormulaVarNoAlpha (σ := σ) (κ := κ) x a φ) →
      Derives (σ := σ) (κ := κ) Γ
        (substFormula (σ := σ) (κ := κ) x (.var a) φ)

/--
Syntactic bridge: under binder-freshness (`a ∉ boundVars φ`), capture-avoiding substitution
by `.var a` coincides with the no-alpha recursion.
-/
theorem substParamToVar_noAlpha_eq_alpha
    (x a : Var) (φ : FormulaH σ κ)
    (ha : a ∉ boundVars (σ := σ) (κ := κ) φ) :
    substFormulaVarNoAlpha (σ := σ) (κ := κ) x a φ =
      substFormula (σ := σ) (κ := κ) x (.var a) φ := by
  symm
  exact substFormula_var_eq_noAlpha_of_not_mem_boundVars
    (σ := σ) (κ := κ) x a φ ha

instance (priority := 62)
    instHasSubstFormulaVarNoAlphaDerivableBridge
    [DecidableEq κ] :
    HasSubstFormulaVarNoAlphaDerivableBridge (σ := σ) (κ := κ) where
  to_noAlpha := by
    intro Γ x a φ ha hDer
    simpa [substParamToVar_noAlpha_eq_alpha (σ := σ) (κ := κ) x a φ ha] using hDer
  of_noAlpha := by
    intro Γ x a φ ha hDer
    simpa [substParamToVar_noAlpha_eq_alpha (σ := σ) (κ := κ) x a φ ha] using hDer

theorem replaceParamWithVar_by_handlers_reduce_to_kpresent_core
    [DecidableEq κ]
    (k : κ) (a : Var)
    {Γ : List (FormulaH σ κ)} {φ : FormulaH σ κ}
    (h : Derives (σ := σ) (κ := κ) Γ φ)
    (hFreshKfree :
      ∀ {ψ : FormulaH σ κ},
        k ∉ paramsFormula (σ := σ) (κ := κ) ψ →
        a ∉ varsFormula (σ := σ) (κ := κ) ψ)
    (hPiI :
      ∀ {Δ : List (FormulaH σ κ)} {x b : Var} {ψ : FormulaH σ κ},
        b ∉ fvContext (σ := σ) (κ := κ) Δ →
        b ∉ varsFormula (σ := σ) (κ := κ) ψ →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.var b) ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi x ψ)))
    (hPiE_param_eq_kpresent_core_conflict :
      ∀ {Δ : List (FormulaH σ κ)} {x : Var} {ψ : FormulaH σ κ},
        k ∈ paramsFormula (σ := σ) (κ := κ) ψ →
        x ∈ fvFormula (σ := σ) (κ := κ) ψ →
        a ∈ boundVars (σ := σ) (κ := κ) ψ →
        x ≠ a →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi x ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.param k) ψ)))
    (hPiE_param_ne_xeq_kpresent :
      ∀ {Δ : List (FormulaH σ κ)} {x : Var} {k' : κ} {ψ : FormulaH σ κ},
        k ∈ paramsFormula (σ := σ) (κ := κ) ψ →
        k' ≠ k →
        x = a →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi x ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.param k') ψ)))
    (hPiE_var_kpresent :
      ∀ {Δ : List (FormulaH σ κ)} {x b : Var} {ψ : FormulaH σ κ},
        k ∈ paramsFormula (σ := σ) (κ := κ) ψ →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi x ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.var b) ψ)))
    (hSigmaI_param_eq_kpresent_core_conflict :
      ∀ {Δ : List (FormulaH σ κ)} {x : Var} {ψ : FormulaH σ κ},
        k ∈ paramsFormula (σ := σ) (κ := κ) ψ →
        x ∈ fvFormula (σ := σ) (κ := κ) ψ →
        a ∈ boundVars (σ := σ) (κ := κ) ψ →
        x ≠ a →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.param k) ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma x ψ)))
    (hSigmaI_param_ne_xeq_kpresent :
      ∀ {Δ : List (FormulaH σ κ)} {x : Var} {k' : κ} {ψ : FormulaH σ κ},
        k ∈ paramsFormula (σ := σ) (κ := κ) ψ →
        k' ≠ k →
        x = a →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.param k') ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma x ψ)))
    (hSigmaI_var_kpresent :
      ∀ {Δ : List (FormulaH σ κ)} {x b : Var} {ψ : FormulaH σ κ},
        k ∈ paramsFormula (σ := σ) (κ := κ) ψ →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.var b) ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma x ψ)))
    (hSigmaE :
      ∀ {Δ : List (FormulaH σ κ)} {x b : Var} {ψ χ : FormulaH σ κ},
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma x ψ)) →
        b ∉ fvContext (σ := σ) (κ := κ) Δ →
        b ∉ varsFormula (σ := σ) (κ := κ) ψ →
        b ∉ fvFormula (σ := σ) (κ := κ) χ →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.var b) ψ :: Δ))
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a χ) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a χ)) :
    Derives (σ := σ) (κ := κ)
      (replaceParamWithVarContext (σ := σ) (κ := κ) k a Γ)
      (replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ) := by
  refine replaceParamWithVar_by_handlers_reduce_to_kpresent_only
    (σ := σ) (κ := κ) (k := k) (a := a) (Γ := Γ) (φ := φ) h
    hFreshKfree hPiI ?_ hPiE_param_ne_xeq_kpresent hPiE_var_kpresent
    ?_ hSigmaI_param_ne_xeq_kpresent hSigmaI_var_kpresent hSigmaE
  ·
    intro Δ x ψ hkψ hPi
    by_cases hxa : x = a
    ·
      exact piE_handler_replaceParamWithVar_param_eq_xeq
        (σ := σ) (κ := κ) (k := k) (a := a) (x := x)
        (Δ := Δ) (ψ := ψ) hxa hPi
    ·
      by_cases hxfv : x ∈ fvFormula (σ := σ) (κ := κ) ψ
      ·
        by_cases haBound : a ∉ boundVars (σ := σ) (κ := κ) ψ
        ·
          exact piE_handler_replaceParamWithVar_param_eq_bound_original
            (σ := σ) (κ := κ) (k := k) (a := a) (x := x)
            (Δ := Δ) (ψ := ψ) haBound hPi
        ·
          have haBoundMem : a ∈ boundVars (σ := σ) (κ := κ) ψ := by
            classical
            exact Classical.not_not.mp haBound
          exact hPiE_param_eq_kpresent_core_conflict
            (Δ := Δ) (x := x) (ψ := ψ) hkψ hxfv haBoundMem hxa hPi
      ·
        exact piE_handler_replaceParamWithVar_param_eq_xnotfv
          (σ := σ) (κ := κ) (k := k) (a := a) (x := x)
          (Δ := Δ) (ψ := ψ) (by simpa using hxfv) hxa hPi
  ·
    intro Δ x ψ hkψ hInst
    by_cases hxa : x = a
    ·
      exact sigmaI_handler_replaceParamWithVar_param_eq_xeq
        (σ := σ) (κ := κ) (k := k) (a := a) (x := x)
        (Δ := Δ) (ψ := ψ) hxa hInst
    ·
      by_cases hxfv : x ∈ fvFormula (σ := σ) (κ := κ) ψ
      ·
        by_cases haBound : a ∉ boundVars (σ := σ) (κ := κ) ψ
        ·
          exact sigmaI_handler_replaceParamWithVar_param_eq_bound_original
            (σ := σ) (κ := κ) (k := k) (a := a) (x := x)
            (Δ := Δ) (ψ := ψ) haBound hInst
        ·
          have haBoundMem : a ∈ boundVars (σ := σ) (κ := κ) ψ := by
            classical
            exact Classical.not_not.mp haBound
          exact hSigmaI_param_eq_kpresent_core_conflict
            (Δ := Δ) (x := x) (ψ := ψ) hkψ hxfv haBoundMem hxa hInst
      ·
        exact sigmaI_handler_replaceParamWithVar_param_eq_xnotfv
          (σ := σ) (κ := κ) (k := k) (a := a) (x := x)
          (Δ := Δ) (ψ := ψ) (by simpa using hxfv) hxa hInst

/--
Convenience wrapper using `HasParamEqKpresentCoreConflictHandlers` for the
`param = k` alpha-conflict frontier (`x ∈ fv` and `a ∈ boundVars`).
-/
theorem replaceParamWithVar_by_handlers_reduce_to_kpresent_core_of_conflict_handlers
    [DecidableEq κ]
    [HasParamEqKpresentCoreConflictHandlers (σ := σ) (κ := κ)]
    (k : κ) (a : Var)
    {Γ : List (FormulaH σ κ)} {φ : FormulaH σ κ}
    (h : Derives (σ := σ) (κ := κ) Γ φ)
    (hFreshKfree :
      ∀ {ψ : FormulaH σ κ},
        k ∉ paramsFormula (σ := σ) (κ := κ) ψ →
        a ∉ varsFormula (σ := σ) (κ := κ) ψ)
    (hPiI :
      ∀ {Δ : List (FormulaH σ κ)} {x b : Var} {ψ : FormulaH σ κ},
        b ∉ fvContext (σ := σ) (κ := κ) Δ →
        b ∉ varsFormula (σ := σ) (κ := κ) ψ →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.var b) ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi x ψ)))
    (hPiE_param_ne_xeq_kpresent :
      ∀ {Δ : List (FormulaH σ κ)} {x : Var} {k' : κ} {ψ : FormulaH σ κ},
        k ∈ paramsFormula (σ := σ) (κ := κ) ψ →
        k' ≠ k →
        x = a →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi x ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.param k') ψ)))
    (hPiE_var_kpresent :
      ∀ {Δ : List (FormulaH σ κ)} {x b : Var} {ψ : FormulaH σ κ},
        k ∈ paramsFormula (σ := σ) (κ := κ) ψ →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi x ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.var b) ψ)))
    (hSigmaI_param_ne_xeq_kpresent :
      ∀ {Δ : List (FormulaH σ κ)} {x : Var} {k' : κ} {ψ : FormulaH σ κ},
        k ∈ paramsFormula (σ := σ) (κ := κ) ψ →
        k' ≠ k →
        x = a →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.param k') ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma x ψ)))
    (hSigmaI_var_kpresent :
      ∀ {Δ : List (FormulaH σ κ)} {x b : Var} {ψ : FormulaH σ κ},
        k ∈ paramsFormula (σ := σ) (κ := κ) ψ →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.var b) ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma x ψ)))
    (hSigmaE :
      ∀ {Δ : List (FormulaH σ κ)} {x b : Var} {ψ χ : FormulaH σ κ},
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma x ψ)) →
        b ∉ fvContext (σ := σ) (κ := κ) Δ →
        b ∉ varsFormula (σ := σ) (κ := κ) ψ →
        b ∉ fvFormula (σ := σ) (κ := κ) χ →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) x (.var b) ψ :: Δ))
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a χ) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a χ)) :
    Derives (σ := σ) (κ := κ)
      (replaceParamWithVarContext (σ := σ) (κ := κ) k a Γ)
      (replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ) := by
  refine replaceParamWithVar_by_handlers_reduce_to_kpresent_core
    (σ := σ) (κ := κ) (k := k) (a := a) (Γ := Γ) (φ := φ) h
    hFreshKfree hPiI ?_ hPiE_param_ne_xeq_kpresent hPiE_var_kpresent
    ?_ hSigmaI_param_ne_xeq_kpresent hSigmaI_var_kpresent hSigmaE
  · exact HasParamEqKpresentCoreConflictHandlers.piE_param_eq_kpresent_core_conflict
      (σ := σ) (κ := κ) k a
  · exact HasParamEqKpresentCoreConflictHandlers.sigmaI_param_eq_kpresent_core_conflict
      (σ := σ) (κ := κ) k a

/--
Concrete `sigmaE`-with-parameter admissibility reducer (explicit branch obligations).

This variant avoids global `k`-free freshness assumptions and instead keeps all
parameter-instantiation obligations explicit in the handler arguments. It is therefore
directly usable in settings where only derivation-local freshness can be established.
-/
theorem sigmaE_param_admissible_reduce_to_kpresent_var
    [DecidableEq κ]
    (k : κ) (a : Var)
    {Γ : List (FormulaH σ κ)} {x : Var} {φ χ : FormulaH σ κ}
    (hkΓ :
      ∀ ψ : FormulaH σ κ, ψ ∈ Γ → k ∉ paramsFormula (σ := σ) (κ := κ) ψ)
    (hkφ : k ∉ paramsFormula (σ := σ) (κ := κ) φ)
    (hkχ : k ∉ paramsFormula (σ := σ) (κ := κ) χ)
    (haΓ : a ∉ fvContext (σ := σ) (κ := κ) Γ)
    (haφ : a ∉ varsFormula (σ := σ) (κ := κ) φ)
    (haχ : a ∉ fvFormula (σ := σ) (κ := κ) χ)
    (hSigma :
      Derives (σ := σ) (κ := κ) Γ (.sigma x φ))
    (hBody :
      Derives (σ := σ) (κ := κ)
        (substFormula (σ := σ) (κ := κ) x (.param k) φ :: Γ) χ)
    (hPiI :
      ∀ {Δ : List (FormulaH σ κ)} {y b : Var} {ψ : FormulaH σ κ},
        b ∉ fvContext (σ := σ) (κ := κ) Δ →
        b ∉ varsFormula (σ := σ) (κ := κ) ψ →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) y (.var b) ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi y ψ)))
    (hPiE_param_eq :
      ∀ {Δ : List (FormulaH σ κ)} {y : Var} {ψ : FormulaH σ κ},
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi y ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) y (.param k) ψ)))
    (hPiE_param_ne :
      ∀ {Δ : List (FormulaH σ κ)} {y : Var} {k' : κ} {ψ : FormulaH σ κ},
        k' ≠ k →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi y ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) y (.param k') ψ)))
    (hPiE_var_kpresent :
      ∀ {Δ : List (FormulaH σ κ)} {y b : Var} {ψ : FormulaH σ κ},
        k ∈ paramsFormula (σ := σ) (κ := κ) ψ →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi y ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) y (.var b) ψ)))
    (hSigmaI_param_eq :
      ∀ {Δ : List (FormulaH σ κ)} {y : Var} {ψ : FormulaH σ κ},
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) y (.param k) ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma y ψ)))
    (hSigmaI_param_ne :
      ∀ {Δ : List (FormulaH σ κ)} {y : Var} {k' : κ} {ψ : FormulaH σ κ},
        k' ≠ k →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) y (.param k') ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma y ψ)))
    (hSigmaI_var_kpresent :
      ∀ {Δ : List (FormulaH σ κ)} {y b : Var} {ψ : FormulaH σ κ},
        k ∈ paramsFormula (σ := σ) (κ := κ) ψ →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) y (.var b) ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma y ψ)))
    (hSigmaE :
      ∀ {Δ : List (FormulaH σ κ)} {y b : Var} {ψ ξ : FormulaH σ κ},
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma y ψ)) →
        b ∉ fvContext (σ := σ) (κ := κ) Δ →
        b ∉ varsFormula (σ := σ) (κ := κ) ψ →
        b ∉ fvFormula (σ := σ) (κ := κ) ξ →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) y (.var b) ψ :: Δ))
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ξ) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ξ)) :
    Derives (σ := σ) (κ := κ) Γ χ := by
  have hTransport :
      Derives (σ := σ) (κ := κ)
        (replaceParamWithVarContext (σ := σ) (κ := κ) k a
          (substFormula (σ := σ) (κ := κ) x (.param k) φ :: Γ))
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a χ) :=
    replaceParamWithVar_by_handlers_reduce_to_kpresent_var
      (σ := σ) (κ := κ) (k := k) (a := a)
      (Γ := substFormula (σ := σ) (κ := κ) x (.param k) φ :: Γ)
      (φ := χ) hBody
      hPiI hPiE_param_eq hPiE_param_ne hPiE_var_kpresent
      hSigmaI_param_eq hSigmaI_param_ne hSigmaI_var_kpresent hSigmaE
  have hContextId :
      ∀ Δ : List (FormulaH σ κ),
        (∀ ψ : FormulaH σ κ, ψ ∈ Δ → k ∉ paramsFormula (σ := σ) (κ := κ) ψ) →
          replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ = Δ := by
    intro Δ hΔ
    induction Δ with
    | nil =>
        simp [replaceParamWithVarContext]
    | cons ψ Δ ih =>
        have hkψ : k ∉ paramsFormula (σ := σ) (κ := κ) ψ := hΔ ψ (by simp)
        have hTail :
            ∀ θ : FormulaH σ κ, θ ∈ Δ → k ∉ paramsFormula (σ := σ) (κ := κ) θ := by
          intro θ hθ
          exact hΔ θ (by simp [hθ])
        have hψEq :
            replaceParamWithVarFormula (σ := σ) (κ := κ) k a ψ = ψ :=
          replaceParamWithVarFormula_eq_of_not_mem_paramsFormula
            (σ := σ) (κ := κ) k a ψ hkψ
        have hΔEq :
            replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ = Δ :=
          ih hTail
        have hΔMapEq :
            List.map (replaceParamWithVarFormula (σ := σ) (κ := κ) k a) Δ = Δ := by
          simpa [replaceParamWithVarContext] using hΔEq
        simp [replaceParamWithVarContext, hψEq, hΔMapEq]
  have hΓEq :
      replaceParamWithVarContext (σ := σ) (κ := κ) k a Γ = Γ :=
    hContextId Γ hkΓ
  have hχEq :
      replaceParamWithVarFormula (σ := σ) (κ := κ) k a χ = χ :=
    replaceParamWithVarFormula_eq_of_not_mem_paramsFormula
      (σ := σ) (κ := κ) k a χ hkχ
  have hφEq :
      replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ = φ :=
    replaceParamWithVarFormula_eq_of_not_mem_paramsFormula
      (σ := σ) (κ := κ) k a φ hkφ
  have haMapped :
      a ∉ varsFormula (σ := σ) (κ := κ)
        (replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ) := by
    simpa [hφEq] using haφ
  have hHeadEq :
      replaceParamWithVarFormula (σ := σ) (κ := κ) k a
        (substFormula (σ := σ) (κ := κ) x (.param k) φ) =
      substFormula (σ := σ) (κ := κ) x (.var a) φ := by
    calc
      replaceParamWithVarFormula (σ := σ) (κ := κ) k a
          (substFormula (σ := σ) (κ := κ) x (.param k) φ) =
        substFormula (σ := σ) (κ := κ) x (.var a)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a φ) := by
            exact replaceParamWithVarFormula_substFormula_param_comm_of_not_mem
              (σ := σ) (κ := κ) k a x φ haMapped
      _ = substFormula (σ := σ) (κ := κ) x (.var a) φ := by
            simp [hφEq]
  have hBodyVarMap :
      Derives (σ := σ) (κ := κ)
        (substFormula (σ := σ) (κ := κ) x (.var a) φ ::
          replaceParamWithVarContext (σ := σ) (κ := κ) k a Γ) χ := by
    simpa [replaceParamWithVarContext, hχEq, hHeadEq] using hTransport
  have hBodyVar :
      Derives (σ := σ) (κ := κ)
        (substFormula (σ := σ) (κ := κ) x (.var a) φ :: Γ) χ := by
    simpa [hΓEq] using hBodyVarMap
  exact Derives.sigmaE hSigma haΓ haφ haχ hBodyVar

/--
Concrete `sigmaE`-with-parameter admissibility reducer.

This consumes `replaceParamWithVar_by_handlers_reduce_to_kpresent_core` on a derivation
`substFormula x (.param k) φ :: Γ ⊢ χ`, then discharges the final step via ordinary `sigmaE`.
  The explicit transport frontier is reduced to the alpha-sensitive `k`-present core
(`x ∈ fvFormula ψ ∧ a ∈ boundVars ψ`) for `param = k` branches; the `x = a` branch is
handled internally.
-/
theorem sigmaE_param_admissible_reduce_to_kpresent
    [DecidableEq κ]
    (k : κ) (a : Var)
    {Γ : List (FormulaH σ κ)} {x : Var} {φ χ : FormulaH σ κ}
    (hkΓ :
      ∀ ψ : FormulaH σ κ, ψ ∈ Γ → k ∉ paramsFormula (σ := σ) (κ := κ) ψ)
    (hkφ : k ∉ paramsFormula (σ := σ) (κ := κ) φ)
    (hkχ : k ∉ paramsFormula (σ := σ) (κ := κ) χ)
    (haΓ : a ∉ fvContext (σ := σ) (κ := κ) Γ)
    (haφ : a ∉ varsFormula (σ := σ) (κ := κ) φ)
    (haχ : a ∉ fvFormula (σ := σ) (κ := κ) χ)
    (hFreshKfree :
      ∀ {ψ : FormulaH σ κ},
        k ∉ paramsFormula (σ := σ) (κ := κ) ψ →
        a ∉ varsFormula (σ := σ) (κ := κ) ψ)
    (hSigma :
      Derives (σ := σ) (κ := κ) Γ (.sigma x φ))
    (hBody :
      Derives (σ := σ) (κ := κ)
        (substFormula (σ := σ) (κ := κ) x (.param k) φ :: Γ) χ)
    (hPiI :
      ∀ {Δ : List (FormulaH σ κ)} {y b : Var} {ψ : FormulaH σ κ},
        b ∉ fvContext (σ := σ) (κ := κ) Δ →
        b ∉ varsFormula (σ := σ) (κ := κ) ψ →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) y (.var b) ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi y ψ)))
    (hPiE_param_eq_kpresent_core_conflict :
      ∀ {Δ : List (FormulaH σ κ)} {y : Var} {ψ : FormulaH σ κ},
        k ∈ paramsFormula (σ := σ) (κ := κ) ψ →
        y ∈ fvFormula (σ := σ) (κ := κ) ψ →
        a ∈ boundVars (σ := σ) (κ := κ) ψ →
        y ≠ a →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi y ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) y (.param k) ψ)))
    (hPiE_param_ne_xeq_kpresent :
      ∀ {Δ : List (FormulaH σ κ)} {y : Var} {k' : κ} {ψ : FormulaH σ κ},
        k ∈ paramsFormula (σ := σ) (κ := κ) ψ →
        k' ≠ k →
        y = a →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi y ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) y (.param k') ψ)))
    (hPiE_var_kpresent :
      ∀ {Δ : List (FormulaH σ κ)} {y b : Var} {ψ : FormulaH σ κ},
        k ∈ paramsFormula (σ := σ) (κ := κ) ψ →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi y ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) y (.var b) ψ)))
    (hSigmaI_param_eq_kpresent_core_conflict :
      ∀ {Δ : List (FormulaH σ κ)} {y : Var} {ψ : FormulaH σ κ},
        k ∈ paramsFormula (σ := σ) (κ := κ) ψ →
        y ∈ fvFormula (σ := σ) (κ := κ) ψ →
        a ∈ boundVars (σ := σ) (κ := κ) ψ →
        y ≠ a →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) y (.param k) ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma y ψ)))
    (hSigmaI_param_ne_xeq_kpresent :
      ∀ {Δ : List (FormulaH σ κ)} {y : Var} {k' : κ} {ψ : FormulaH σ κ},
        k ∈ paramsFormula (σ := σ) (κ := κ) ψ →
        k' ≠ k →
        y = a →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) y (.param k') ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma y ψ)))
    (hSigmaI_var_kpresent :
      ∀ {Δ : List (FormulaH σ κ)} {y b : Var} {ψ : FormulaH σ κ},
        k ∈ paramsFormula (σ := σ) (κ := κ) ψ →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) y (.var b) ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma y ψ)))
    (hSigmaE :
      ∀ {Δ : List (FormulaH σ κ)} {y b : Var} {ψ ξ : FormulaH σ κ},
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma y ψ)) →
        b ∉ fvContext (σ := σ) (κ := κ) Δ →
        b ∉ varsFormula (σ := σ) (κ := κ) ψ →
        b ∉ fvFormula (σ := σ) (κ := κ) ξ →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) y (.var b) ψ :: Δ))
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ξ) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ξ)) :
    Derives (σ := σ) (κ := κ) Γ χ := by
  have hPiE_param_eq :
      ∀ {Δ : List (FormulaH σ κ)} {y : Var} {ψ : FormulaH σ κ},
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi y ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) y (.param k) ψ)) := by
    intro Δ y ψ hPi
    by_cases hkψ : k ∈ paramsFormula (σ := σ) (κ := κ) ψ
    · by_cases hya : y = a
      ·
        exact piE_handler_replaceParamWithVar_param_eq_xeq
          (σ := σ) (κ := κ) (k := k) (a := a) (x := y)
          (Δ := Δ) (ψ := ψ) hya hPi
      · by_cases hyfv : y ∈ fvFormula (σ := σ) (κ := κ) ψ
        ·
          by_cases haBound : a ∉ boundVars (σ := σ) (κ := κ) ψ
          ·
            exact piE_handler_replaceParamWithVar_param_eq_bound_original
              (σ := σ) (κ := κ) (k := k) (a := a) (x := y)
              (Δ := Δ) (ψ := ψ) haBound hPi
          ·
            have haBoundMem : a ∈ boundVars (σ := σ) (κ := κ) ψ := by
              classical
              exact Classical.not_not.mp haBound
            exact hPiE_param_eq_kpresent_core_conflict
              (Δ := Δ) (y := y) (ψ := ψ) hkψ hyfv haBoundMem hya hPi
        · exact piE_handler_replaceParamWithVar_param_eq_xnotfv
            (σ := σ) (κ := κ) (k := k) (a := a) (x := y)
            (Δ := Δ) (ψ := ψ) (by simpa using hyfv) hya hPi
    · exact piE_handler_replaceParamWithVar_param_eq_param_free
        (σ := σ) (κ := κ) (k := k) (a := a) (x := y)
        (Δ := Δ) (ψ := ψ) (by simpa using hkψ)
        (hFreshKfree (by simpa using hkψ)) hPi
  have hPiE_param_ne :
      ∀ {Δ : List (FormulaH σ κ)} {y : Var} {k' : κ} {ψ : FormulaH σ κ},
        k' ≠ k →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi y ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) y (.param k') ψ)) := by
    intro Δ y k' ψ hk' hPi
    by_cases hya : y = a
    · by_cases hkψ : k ∈ paramsFormula (σ := σ) (κ := κ) ψ
      · exact hPiE_param_ne_xeq_kpresent
          (Δ := Δ) (y := y) (k' := k') (ψ := ψ) hkψ hk' hya hPi
      · exact piE_handler_replaceParamWithVar_param_ne_param_free
          (σ := σ) (κ := κ) (k := k) (k' := k') (a := a) (x := y)
          (Δ := Δ) (ψ := ψ) hk' (by simpa using hkψ) hPi
    · exact piE_handler_replaceParamWithVar_param_ne
        (σ := σ) (κ := κ) (k := k) (k' := k') (a := a) (x := y)
        (Δ := Δ) (ψ := ψ) hk' hya hPi
  have hSigmaI_param_eq :
      ∀ {Δ : List (FormulaH σ κ)} {y : Var} {ψ : FormulaH σ κ},
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) y (.param k) ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma y ψ)) := by
    intro Δ y ψ hInst
    by_cases hkψ : k ∈ paramsFormula (σ := σ) (κ := κ) ψ
    · by_cases hya : y = a
      ·
        exact sigmaI_handler_replaceParamWithVar_param_eq_xeq
          (σ := σ) (κ := κ) (k := k) (a := a) (x := y)
          (Δ := Δ) (ψ := ψ) hya hInst
      · by_cases hyfv : y ∈ fvFormula (σ := σ) (κ := κ) ψ
        ·
          by_cases haBound : a ∉ boundVars (σ := σ) (κ := κ) ψ
          ·
            exact sigmaI_handler_replaceParamWithVar_param_eq_bound_original
              (σ := σ) (κ := κ) (k := k) (a := a) (x := y)
              (Δ := Δ) (ψ := ψ) haBound hInst
          ·
            have haBoundMem : a ∈ boundVars (σ := σ) (κ := κ) ψ := by
              classical
              exact Classical.not_not.mp haBound
            exact hSigmaI_param_eq_kpresent_core_conflict
              (Δ := Δ) (y := y) (ψ := ψ) hkψ hyfv haBoundMem hya hInst
        · exact sigmaI_handler_replaceParamWithVar_param_eq_xnotfv
            (σ := σ) (κ := κ) (k := k) (a := a) (x := y)
            (Δ := Δ) (ψ := ψ) (by simpa using hyfv) hya hInst
    · exact sigmaI_handler_replaceParamWithVar_param_eq_param_free
        (σ := σ) (κ := κ) (k := k) (a := a) (x := y)
        (Δ := Δ) (ψ := ψ) (by simpa using hkψ)
        (hFreshKfree (by simpa using hkψ)) hInst
  have hSigmaI_param_ne :
      ∀ {Δ : List (FormulaH σ κ)} {y : Var} {k' : κ} {ψ : FormulaH σ κ},
        k' ≠ k →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) y (.param k') ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma y ψ)) := by
    intro Δ y k' ψ hk' hInst
    by_cases hya : y = a
    · by_cases hkψ : k ∈ paramsFormula (σ := σ) (κ := κ) ψ
      · exact hSigmaI_param_ne_xeq_kpresent
          (Δ := Δ) (y := y) (k' := k') (ψ := ψ) hkψ hk' hya hInst
      · exact sigmaI_handler_replaceParamWithVar_param_ne_param_free
          (σ := σ) (κ := κ) (k := k) (k' := k') (a := a) (x := y)
          (Δ := Δ) (ψ := ψ) hk' (by simpa using hkψ) hInst
    · exact sigmaI_handler_replaceParamWithVar_param_ne
        (σ := σ) (κ := κ) (k := k) (k' := k') (a := a) (x := y)
        (Δ := Δ) (ψ := ψ) hk' hya hInst
  exact sigmaE_param_admissible_reduce_to_kpresent_var
    (σ := σ) (κ := κ) (k := k) (a := a)
    (Γ := Γ) (x := x) (φ := φ) (χ := χ)
    hkΓ hkφ hkχ haΓ haφ haχ hSigma hBody
    hPiI hPiE_param_eq hPiE_param_ne hPiE_var_kpresent
    hSigmaI_param_eq hSigmaI_param_ne hSigmaI_var_kpresent hSigmaE

/--
Convenience wrapper for `sigmaE_param_admissible_reduce_to_kpresent` using
`HasParamEqKpresentCoreConflictHandlers` for the remaining `param = k`
alpha-conflict obligations.
-/
theorem sigmaE_param_admissible_reduce_to_kpresent_of_conflict_handlers
    [DecidableEq κ]
    [HasParamEqKpresentCoreConflictHandlers (σ := σ) (κ := κ)]
    (k : κ) (a : Var)
    {Γ : List (FormulaH σ κ)} {x : Var} {φ χ : FormulaH σ κ}
    (hkΓ :
      ∀ ψ : FormulaH σ κ, ψ ∈ Γ → k ∉ paramsFormula (σ := σ) (κ := κ) ψ)
    (hkφ : k ∉ paramsFormula (σ := σ) (κ := κ) φ)
    (hkχ : k ∉ paramsFormula (σ := σ) (κ := κ) χ)
    (haΓ : a ∉ fvContext (σ := σ) (κ := κ) Γ)
    (haφ : a ∉ varsFormula (σ := σ) (κ := κ) φ)
    (haχ : a ∉ fvFormula (σ := σ) (κ := κ) χ)
    (hFreshKfree :
      ∀ {ψ : FormulaH σ κ},
        k ∉ paramsFormula (σ := σ) (κ := κ) ψ →
        a ∉ varsFormula (σ := σ) (κ := κ) ψ)
    (hSigma :
      Derives (σ := σ) (κ := κ) Γ (.sigma x φ))
    (hBody :
      Derives (σ := σ) (κ := κ)
        (substFormula (σ := σ) (κ := κ) x (.param k) φ :: Γ) χ)
    (hPiI :
      ∀ {Δ : List (FormulaH σ κ)} {y b : Var} {ψ : FormulaH σ κ},
        b ∉ fvContext (σ := σ) (κ := κ) Δ →
        b ∉ varsFormula (σ := σ) (κ := κ) ψ →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) y (.var b) ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi y ψ)))
    (hPiE_param_ne_xeq_kpresent :
      ∀ {Δ : List (FormulaH σ κ)} {y : Var} {k' : κ} {ψ : FormulaH σ κ},
        k ∈ paramsFormula (σ := σ) (κ := κ) ψ →
        k' ≠ k →
        y = a →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi y ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) y (.param k') ψ)))
    (hPiE_var_kpresent :
      ∀ {Δ : List (FormulaH σ κ)} {y b : Var} {ψ : FormulaH σ κ},
        k ∈ paramsFormula (σ := σ) (κ := κ) ψ →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.pi y ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) y (.var b) ψ)))
    (hSigmaI_param_ne_xeq_kpresent :
      ∀ {Δ : List (FormulaH σ κ)} {y : Var} {k' : κ} {ψ : FormulaH σ κ},
        k ∈ paramsFormula (σ := σ) (κ := κ) ψ →
        k' ≠ k →
        y = a →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) y (.param k') ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma y ψ)))
    (hSigmaI_var_kpresent :
      ∀ {Δ : List (FormulaH σ κ)} {y b : Var} {ψ : FormulaH σ κ},
        k ∈ paramsFormula (σ := σ) (κ := κ) ψ →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) y (.var b) ψ)) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma y ψ)))
    (hSigmaE :
      ∀ {Δ : List (FormulaH σ κ)} {y b : Var} {ψ ξ : FormulaH σ κ},
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a (.sigma y ψ)) →
        b ∉ fvContext (σ := σ) (κ := κ) Δ →
        b ∉ varsFormula (σ := σ) (κ := κ) ψ →
        b ∉ fvFormula (σ := σ) (κ := κ) ξ →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a
            (substFormula (σ := σ) (κ := κ) y (.var b) ψ :: Δ))
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ξ) →
        Derives (σ := σ) (κ := κ)
          (replaceParamWithVarContext (σ := σ) (κ := κ) k a Δ)
          (replaceParamWithVarFormula (σ := σ) (κ := κ) k a ξ)) :
    Derives (σ := σ) (κ := κ) Γ χ := by
  refine sigmaE_param_admissible_reduce_to_kpresent
    (σ := σ) (κ := κ) (k := k) (a := a)
    (Γ := Γ) (x := x) (φ := φ) (χ := χ)
    hkΓ hkφ hkχ haΓ haφ haχ hFreshKfree hSigma hBody hPiI ?_
    hPiE_param_ne_xeq_kpresent hPiE_var_kpresent ?_
    hSigmaI_param_ne_xeq_kpresent hSigmaI_var_kpresent hSigmaE
  · exact HasParamEqKpresentCoreConflictHandlers.piE_param_eq_kpresent_core_conflict
      (σ := σ) (κ := κ) k a
  · exact HasParamEqKpresentCoreConflictHandlers.sigmaI_param_eq_kpresent_core_conflict
      (σ := σ) (κ := κ) k a

end Derives

end NDH
end Noneism
end HeytingLean
