import HeytingLean.Noneism.ProofTheory.NDH

/-!
# Noneism.ProofTheory.Quantifiers.NDHWitness

Track J / Phase 2 (M2): a Henkin-style witness layer for existential elimination.

Motivation:
- In open contexts, `sigmaE`'s eigenvariable freshness constraint is exactly where internal Kripke
  completeness gets stuck (family-level witness insertion/extraction).
- Henkin's classic move is to introduce *fresh constants* as witnesses instead of fresh variables.
- In our Henkin term language `TermH κ`, parameters `κ` play the role of constants.

This file defines a derivation judgment `NDH.DerivesWit` for formulas over
`κ := Syntax.Henkin.WitParams κw κ0 = Sum κw κ0`, where `Sum.inl` is reserved for witness
constants (`κw`) and `Sum.inr` for ambient parameters (`κ0`).

The key new rule is `sigmaE_wit`: it eliminates `sigma` using a fresh *witness constant* rather
than a fresh variable.

This is intended as a stable interface for later completeness work; it does not yet rewire the
existing completeness proof to use this judgment.
-/

namespace HeytingLean
namespace Noneism
namespace NDH

open Formula
open Syntax.Henkin

/-! ## Parameter support of Henkin contexts -/

/-- Henkin-parameter support of a context. -/
def paramsContext {σ κ : Type} [DecidableEq κ] (Γ : List (FormulaH σ κ)) : Finset κ :=
  Γ.foldr (fun φ acc => Syntax.Henkin.paramsFormula (σ := σ) (κ := κ) φ ∪ acc) ∅

@[simp] theorem paramsContext_nil {σ κ : Type} [DecidableEq κ] :
    paramsContext (σ := σ) (κ := κ) ([] : List (FormulaH σ κ)) = ∅ := rfl

@[simp] theorem paramsContext_cons {σ κ : Type} [DecidableEq κ]
    (φ : FormulaH σ κ) (Γ : List (FormulaH σ κ)) :
    paramsContext (σ := σ) (κ := κ) (φ :: Γ) =
      Syntax.Henkin.paramsFormula (σ := σ) (κ := κ) φ ∪ paramsContext (σ := σ) (κ := κ) Γ := by
  simp [paramsContext]

theorem mem_paramsContext_iff {σ κ : Type} [DecidableEq κ] {k : κ} {Γ : List (FormulaH σ κ)} :
    k ∈ paramsContext (σ := σ) (κ := κ) Γ ↔
      ∃ ψ, ψ ∈ Γ ∧ k ∈ Syntax.Henkin.paramsFormula (σ := σ) (κ := κ) ψ := by
  induction Γ with
  | nil =>
      simp [paramsContext]
  | cons φ Γ ih =>
      constructor
      · intro hk
        simp [paramsContext_cons, Finset.mem_union] at hk
        rcases hk with hk | hk
        · exact ⟨φ, by simp, hk⟩
        · rcases (ih.1 hk) with ⟨ψ, hψ, hkψ⟩
          exact ⟨ψ, by simp [hψ], hkψ⟩
      · rintro ⟨ψ, hψ, hkψ⟩
        simp [paramsContext_cons, Finset.mem_union]
        rcases List.mem_cons.1 hψ with hEq | hTail
        · subst hEq
          exact Or.inl hkψ
        · exact Or.inr ((ih.2) ⟨ψ, hTail, hkψ⟩)

/-! ## `paramsFormula` under parameter renaming -/

open scoped Classical

@[simp] theorem paramsTerm_mapParamsTerm
    {κ κ' : Type} [DecidableEq κ] [DecidableEq κ']
    (f : κ → κ') (t : TermH κ) :
    Syntax.Henkin.paramsTerm (κ := κ') (Syntax.Henkin.mapParamsTerm f t) =
      (Syntax.Henkin.paramsTerm (κ := κ) t).image f := by
  cases t with
  | var x =>
      simp [Syntax.Henkin.paramsTerm, Syntax.Henkin.mapParamsTerm]
  | param k =>
      simp [Syntax.Henkin.paramsTerm, Syntax.Henkin.mapParamsTerm]

@[simp] theorem paramsTerms_mapParamsTerms
    {κ κ' : Type} [DecidableEq κ] [DecidableEq κ']
    (f : κ → κ') (ts : List (TermH κ)) :
    Syntax.Henkin.paramsTerms (κ := κ') (Syntax.Henkin.mapParamsTerms f ts) =
      (Syntax.Henkin.paramsTerms (κ := κ) ts).image f := by
  induction ts with
  | nil =>
      simp [Syntax.Henkin.paramsTerms, Syntax.Henkin.mapParamsTerms]
  | cons t ts ih =>
      have ih' :
          Syntax.Henkin.paramsTerms (κ := κ') (List.map (Syntax.Henkin.mapParamsTerm f) ts) =
            (Syntax.Henkin.paramsTerms (κ := κ) ts).image f := by
        simpa [Syntax.Henkin.mapParamsTerms] using ih
      simp [Syntax.Henkin.mapParamsTerms, Syntax.Henkin.paramsTerms_cons,
        Finset.image_union, ih']

@[simp] theorem paramsFormula_mapParamsFormula
    {σ κ κ' : Type} [DecidableEq κ] [DecidableEq κ']
    (f : κ → κ') (φ : FormulaH σ κ) :
    Syntax.Henkin.paramsFormula (σ := σ) (κ := κ') (Syntax.Henkin.mapParamsFormula (σ := σ) f φ) =
      (Syntax.Henkin.paramsFormula (σ := σ) (κ := κ) φ).image f := by
  induction φ with
  | top =>
      simp [Syntax.Henkin.paramsFormula, Syntax.Henkin.mapParamsFormula]
  | bot =>
      simp [Syntax.Henkin.paramsFormula, Syntax.Henkin.mapParamsFormula]
  | pred p args =>
      simp [Syntax.Henkin.paramsFormula, Syntax.Henkin.mapParamsFormula]
  | eExists t =>
      simp [Syntax.Henkin.paramsFormula, Syntax.Henkin.mapParamsFormula]
  | not φ ih =>
      simp [Syntax.Henkin.paramsFormula, Syntax.Henkin.mapParamsFormula, ih]
  | and φ ψ ihφ ihψ =>
      simp [Syntax.Henkin.paramsFormula, Syntax.Henkin.mapParamsFormula, ihφ, ihψ, Finset.image_union]
  | or φ ψ ihφ ihψ =>
      simp [Syntax.Henkin.paramsFormula, Syntax.Henkin.mapParamsFormula, ihφ, ihψ, Finset.image_union]
  | imp φ ψ ihφ ihψ =>
      simp [Syntax.Henkin.paramsFormula, Syntax.Henkin.mapParamsFormula, ihφ, ihψ, Finset.image_union]
  | sigma x φ ih =>
      simp [Syntax.Henkin.paramsFormula, Syntax.Henkin.mapParamsFormula, ih]
  | pi x φ ih =>
      simp [Syntax.Henkin.paramsFormula, Syntax.Henkin.mapParamsFormula, ih]

@[simp] theorem paramsContext_mapParamsContext
    {σ κ κ' : Type} [DecidableEq κ] [DecidableEq κ']
    (f : κ → κ') (Γ : List (FormulaH σ κ)) :
    paramsContext (σ := σ) (κ := κ') (mapParamsContext (σ := σ) (κ := κ) f Γ) =
      (paramsContext (σ := σ) (κ := κ) Γ).image f := by
  induction Γ with
  | nil =>
      simp [paramsContext, mapParamsContext]
  | cons φ Γ ih =>
      have ih' :
          paramsContext (σ := σ) (κ := κ')
              (List.map (Syntax.Henkin.mapParamsFormula (σ := σ) f) Γ) =
            (paramsContext (σ := σ) (κ := κ) Γ).image f := by
        simpa [mapParamsContext] using ih
      simp [mapParamsContext, paramsContext_cons, Finset.image_union, ih']

/-! ## Witness-constant derivations -/

section

variable {σ κw κ0 : Type}

/--
Henkin witness derivations.

`Sum.inl` parameters are reserved for "fresh witness constants"; the key constructor is
`sigmaE_wit`, which eliminates `sigma` using such a witness constant rather than an eigenvariable.
-/
inductive DerivesWit : List (FormulaH σ (WitParams κw κ0)) → FormulaH σ (WitParams κw κ0) → Prop
  | hyp {Γ : List (FormulaH σ (WitParams κw κ0))} {φ : FormulaH σ (WitParams κw κ0)} :
      φ ∈ Γ → DerivesWit Γ φ
  | topI {Γ : List (FormulaH σ (WitParams κw κ0))} :
      DerivesWit Γ .top
  | botE {Γ : List (FormulaH σ (WitParams κw κ0))} {φ : FormulaH σ (WitParams κw κ0)} :
      DerivesWit Γ .bot → DerivesWit Γ φ
  | andI {Γ : List (FormulaH σ (WitParams κw κ0))} {φ ψ : FormulaH σ (WitParams κw κ0)} :
      DerivesWit Γ φ → DerivesWit Γ ψ → DerivesWit Γ (.and φ ψ)
  | andEL {Γ : List (FormulaH σ (WitParams κw κ0))} {φ ψ : FormulaH σ (WitParams κw κ0)} :
      DerivesWit Γ (.and φ ψ) → DerivesWit Γ φ
  | andER {Γ : List (FormulaH σ (WitParams κw κ0))} {φ ψ : FormulaH σ (WitParams κw κ0)} :
      DerivesWit Γ (.and φ ψ) → DerivesWit Γ ψ
  | orIL {Γ : List (FormulaH σ (WitParams κw κ0))} {φ ψ : FormulaH σ (WitParams κw κ0)} :
      DerivesWit Γ φ → DerivesWit Γ (.or φ ψ)
  | orIR {Γ : List (FormulaH σ (WitParams κw κ0))} {φ ψ : FormulaH σ (WitParams κw κ0)} :
      DerivesWit Γ ψ → DerivesWit Γ (.or φ ψ)
  | orE {Γ : List (FormulaH σ (WitParams κw κ0))} {φ ψ χ : FormulaH σ (WitParams κw κ0)} :
      DerivesWit Γ (.or φ ψ) →
      DerivesWit (φ :: Γ) χ →
      DerivesWit (ψ :: Γ) χ →
      DerivesWit Γ χ
  | impI {Γ : List (FormulaH σ (WitParams κw κ0))} {φ ψ : FormulaH σ (WitParams κw κ0)} :
      DerivesWit (φ :: Γ) ψ → DerivesWit Γ (.imp φ ψ)
  | impE {Γ : List (FormulaH σ (WitParams κw κ0))} {φ ψ : FormulaH σ (WitParams κw κ0)} :
      DerivesWit Γ (.imp φ ψ) → DerivesWit Γ φ → DerivesWit Γ ψ
  | notI {Γ : List (FormulaH σ (WitParams κw κ0))} {φ : FormulaH σ (WitParams κw κ0)} :
      DerivesWit (φ :: Γ) .bot → DerivesWit Γ (.not φ)
  | notE {Γ : List (FormulaH σ (WitParams κw κ0))} {φ : FormulaH σ (WitParams κw κ0)} :
      DerivesWit Γ (.not φ) → DerivesWit Γ φ → DerivesWit Γ .bot
  | piI {Γ : List (FormulaH σ (WitParams κw κ0))} {x a : Var} {φ : FormulaH σ (WitParams κw κ0)} :
      a ∉ fvContext (σ := σ) (κ := WitParams κw κ0) Γ →
      a ∉ Syntax.Henkin.varsFormula (σ := σ) (κ := WitParams κw κ0) φ →
      DerivesWit Γ (Syntax.Henkin.substFormula (σ := σ) (κ := WitParams κw κ0) x (.var a) φ) →
      DerivesWit Γ (.pi x φ)
  | piE {Γ : List (FormulaH σ (WitParams κw κ0))} {x : Var} {t : TermH (WitParams κw κ0)}
      {φ : FormulaH σ (WitParams κw κ0)} :
      DerivesWit Γ (.pi x φ) →
      DerivesWit Γ (Syntax.Henkin.substFormula (σ := σ) (κ := WitParams κw κ0) x t φ)
  | sigmaI {Γ : List (FormulaH σ (WitParams κw κ0))} {x : Var} {t : TermH (WitParams κw κ0)}
      {φ : FormulaH σ (WitParams κw κ0)} :
      DerivesWit Γ (Syntax.Henkin.substFormula (σ := σ) (κ := WitParams κw κ0) x t φ) →
      DerivesWit Γ (.sigma x φ)
  | sigmaE {Γ : List (FormulaH σ (WitParams κw κ0))} {x a : Var}
      {φ χ : FormulaH σ (WitParams κw κ0)} :
      DerivesWit Γ (.sigma x φ) →
      a ∉ fvContext (σ := σ) (κ := WitParams κw κ0) Γ →
      a ∉ Syntax.Henkin.varsFormula (σ := σ) (κ := WitParams κw κ0) φ →
      a ∉ Syntax.Henkin.fvFormula (σ := σ) (κ := WitParams κw κ0) χ →
      DerivesWit (Syntax.Henkin.substFormula (σ := σ) (κ := WitParams κw κ0) x (.var a) φ :: Γ) χ →
      DerivesWit Γ χ
  | sigmaE_wit
      {Γ : List (FormulaH σ (WitParams κw κ0))} {x : Var} {w : κw}
      {φ χ : FormulaH σ (WitParams κw κ0)} :
      DerivesWit Γ (.sigma x φ) →
      (Sum.inl w : WitParams κw κ0) ∉ paramsContext (σ := σ) (κ := WitParams κw κ0) Γ →
      (Sum.inl w : WitParams κw κ0) ∉
        Syntax.Henkin.paramsFormula (σ := σ) (κ := WitParams κw κ0) χ →
      DerivesWit (Syntax.Henkin.witnessBodyW (σ := σ) (κw := κw) (κ := κ0) x w φ :: Γ) χ →
      DerivesWit Γ χ
  | wk {Γ Δ : List (FormulaH σ (WitParams κw κ0))} {φ : FormulaH σ (WitParams κw κ0)} :
      DerivesWit Γ φ →
      Γ ⊆ Δ →
      DerivesWit Δ φ

namespace DerivesWit

/-- Embed ordinary Henkin derivations into witness derivations. -/
theorem ofDerives {Γ : List (FormulaH σ (WitParams κw κ0))} {φ : FormulaH σ (WitParams κw κ0)} :
    NDH.Derives (σ := σ) (κ := WitParams κw κ0) Γ φ → DerivesWit Γ φ := by
  intro h
  induction h with
  | hyp hmem =>
      exact DerivesWit.hyp hmem
  | topI =>
      exact DerivesWit.topI
  | botE h ih =>
      exact DerivesWit.botE ih
  | andI h1 h2 ih1 ih2 =>
      exact DerivesWit.andI ih1 ih2
  | andEL h ih =>
      exact DerivesWit.andEL ih
  | andER h ih =>
      exact DerivesWit.andER ih
  | orIL h ih =>
      exact DerivesWit.orIL ih
  | orIR h ih =>
      exact DerivesWit.orIR ih
  | orE hOr hL hR ihOr ihL ihR =>
      exact DerivesWit.orE ihOr ihL ihR
  | impI h ih =>
      exact DerivesWit.impI ih
  | impE h1 h2 ih1 ih2 =>
      exact DerivesWit.impE ih1 ih2
  | notI h ih =>
      exact DerivesWit.notI ih
  | notE h1 h2 ih1 ih2 =>
      exact DerivesWit.notE ih1 ih2
  | piI haΓ haVars h ih =>
      exact DerivesWit.piI haΓ haVars ih
  | piE h ih =>
      exact DerivesWit.piE ih
  | sigmaI h ih =>
      exact DerivesWit.sigmaI ih
  | sigmaE hSigma haΓ haVars haχ hDer ihSigma ihDer =>
      exact DerivesWit.sigmaE ihSigma haΓ haVars haχ ihDer
  | wk h hSub ih =>
      exact DerivesWit.wk ih hSub

theorem weaken {Γ Δ : List (FormulaH σ (WitParams κw κ0))} {φ : FormulaH σ (WitParams κw κ0)}
    (h : DerivesWit (σ := σ) (κw := κw) (κ0 := κ0) Γ φ)
    (hSub : Γ ⊆ Δ) :
    DerivesWit (σ := σ) (κw := κw) (κ0 := κ0) Δ φ :=
  DerivesWit.wk h hSub

/--
Parameter renaming for witness derivations, provided the renaming on both witness parameters and
ambient parameters is injective.

This is the Track J workhorse: it lets us consistently "refresh" finitely many witness constants
in a derivation without touching variable eigenconditions.
-/
theorem mapWitParams
    {κw' κ0' : Type}
    (fw : κw → κw') (fk : κ0 → κ0')
    (hfw : Function.Injective fw) (hfk : Function.Injective fk)
    {Γ : List (FormulaH σ (WitParams κw κ0))}
    {φ : FormulaH σ (WitParams κw κ0)} :
    DerivesWit (σ := σ) (κw := κw) (κ0 := κ0) Γ φ →
      DerivesWit (σ := σ) (κw := κw') (κ0 := κ0')
        (mapParamsContext (σ := σ) (κ := WitParams κw κ0)
          (f := Sum.map fw fk) Γ)
        (Syntax.Henkin.mapParamsFormula (σ := σ) (f := Sum.map fw fk) φ) := by
  classical
  intro h
  -- Keep `hfk` in the dependency set: later uses will need ambient-parameter injectivity too.
  have hfk_used : Function.Injective fk := hfk
  clear hfk_used
  let f : WitParams κw κ0 → WitParams κw' κ0' := Sum.map fw fk

  -- Freshness transport for witness-constants through `Finset.image`.
  have hFreshImage :
      ∀ {S : Finset (WitParams κw κ0)} {w : κw},
        (Sum.inl w : WitParams κw κ0) ∉ S →
          (Sum.inl (fw w) : WitParams κw' κ0') ∉ S.image f := by
    intro S w hw
    intro hmem
    rcases Finset.mem_image.1 hmem with ⟨a, haS, haEq⟩
    cases a with
    | inl wa =>
        have : fw wa = fw w := by
          simpa [f] using Sum.inl.inj haEq
        have hwa : wa = w := hfw this
        subst hwa
        exact hw haS
    | inr ka =>
        -- `Sum.map` preserves `inl/inr`, so this is impossible.
        cases haEq

  -- Main induction on the derivation.
  induction h with
  | hyp hmem =>
      refine DerivesWit.hyp ?_
      -- `mapParamsContext f Γ` is `List.map (mapParamsFormula f) Γ`.
      exact List.mem_map.2 ⟨_, hmem, rfl⟩
  | topI =>
      exact DerivesWit.topI
  | botE h ih =>
      exact DerivesWit.botE ih
  | andI h1 h2 ih1 ih2 =>
      exact DerivesWit.andI ih1 ih2
  | andEL h ih =>
      exact DerivesWit.andEL ih
  | andER h ih =>
      exact DerivesWit.andER ih
  | orIL h ih =>
      exact DerivesWit.orIL ih
  | orIR h ih =>
      exact DerivesWit.orIR ih
  | orE hOr hL hR ihOr ihL ihR =>
      exact DerivesWit.orE ihOr ihL ihR
  | impI h ih =>
      exact DerivesWit.impI ih
  | impE h1 h2 ih1 ih2 =>
      exact DerivesWit.impE ih1 ih2
  | notI h ih =>
      exact DerivesWit.notI ih
  | notE h1 h2 ih1 ih2 =>
      exact DerivesWit.notE ih1 ih2
  | piI haΓ haVars hInst ihInst =>
      -- Parameter renaming does not affect variable eigenconditions.
      rename_i Γ x a φ
      have haΓ' :
          a ∉ fvContext (σ := σ) (κ := WitParams κw' κ0')
            (mapParamsContext (σ := σ) (κ := WitParams κw κ0) (f := f) Γ) := by
        simpa [f, fvContext_mapParamsContext] using haΓ
      have haVars' :
          a ∉ Syntax.Henkin.varsFormula (σ := σ) (κ := WitParams κw' κ0')
            (Syntax.Henkin.mapParamsFormula (σ := σ) (f := f) φ) := by
        simpa [f] using haVars
      refine DerivesWit.piI (σ := σ) (κw := κw') (κ0 := κ0')
        (Γ := mapParamsContext (σ := σ) (κ := WitParams κw κ0) (f := f) Γ)
        (x := x) (a := a)
        (φ := Syntax.Henkin.mapParamsFormula (σ := σ) (f := f) φ)
        haΓ' haVars' ?_
      simpa [f, Syntax.Henkin.mapParamsFormula_substFormula] using ihInst
  | piE hPi ihPi =>
      rename_i Γ x t φ
      have hPi' :
          DerivesWit (σ := σ) (κw := κw') (κ0 := κ0')
            (mapParamsContext (σ := σ) (κ := WitParams κw κ0) (f := f) Γ)
            (.pi x (Syntax.Henkin.mapParamsFormula (σ := σ) (f := f) φ)) := by
        simpa [f] using ihPi
      have h' :
          DerivesWit (σ := σ) (κw := κw') (κ0 := κ0')
            (mapParamsContext (σ := σ) (κ := WitParams κw κ0) (f := f) Γ)
            (Syntax.Henkin.substFormula (σ := σ) (κ := WitParams κw' κ0') x
              (Syntax.Henkin.mapParamsTerm f t)
              (Syntax.Henkin.mapParamsFormula (σ := σ) (f := f) φ)) :=
        DerivesWit.piE (σ := σ) (κw := κw') (κ0 := κ0')
          (Γ := mapParamsContext (σ := σ) (κ := WitParams κw κ0) (f := f) Γ)
          (x := x) (t := Syntax.Henkin.mapParamsTerm f t)
          (φ := Syntax.Henkin.mapParamsFormula (σ := σ) (f := f) φ)
          hPi'
      simpa [f, Syntax.Henkin.mapParamsFormula_substFormula] using h'
  | sigmaI hInst ihInst =>
      rename_i Γ x t φ
      refine DerivesWit.sigmaI (σ := σ) (κw := κw') (κ0 := κ0')
        (Γ := mapParamsContext (σ := σ) (κ := WitParams κw κ0) (f := f) Γ)
        (x := x) (t := Syntax.Henkin.mapParamsTerm f t)
        (φ := Syntax.Henkin.mapParamsFormula (σ := σ) (f := f) φ) ?_
      simpa [f, Syntax.Henkin.mapParamsFormula_substFormula] using ihInst
  | sigmaE hSigma haΓ haVars haχ hDer ihSigma ihDer =>
      rename_i Γ x a φ χ
      have haΓ' :
          a ∉ fvContext (σ := σ) (κ := WitParams κw' κ0')
            (mapParamsContext (σ := σ) (κ := WitParams κw κ0) (f := f) Γ) := by
        simpa [f, fvContext_mapParamsContext] using haΓ
      have haVars' :
          a ∉ Syntax.Henkin.varsFormula (σ := σ) (κ := WitParams κw' κ0')
            (Syntax.Henkin.mapParamsFormula (σ := σ) (f := f) φ) := by
        simpa [f] using haVars
      have haχ' :
          a ∉ Syntax.Henkin.fvFormula (σ := σ) (κ := WitParams κw' κ0')
            (Syntax.Henkin.mapParamsFormula (σ := σ) (f := f) χ) := by
        simpa [f] using haχ
      have hSigma' :
          DerivesWit (σ := σ) (κw := κw') (κ0 := κ0')
            (mapParamsContext (σ := σ) (κ := WitParams κw κ0) (f := f) Γ)
            (.sigma x (Syntax.Henkin.mapParamsFormula (σ := σ) (f := f) φ)) := by
        simpa [f] using ihSigma
      have ihDer' :
          DerivesWit (σ := σ) (κw := κw') (κ0 := κ0')
            (Syntax.Henkin.substFormula (σ := σ) (κ := WitParams κw' κ0') x (.var a)
                (Syntax.Henkin.mapParamsFormula (σ := σ) (f := f) φ)
              :: mapParamsContext (σ := σ) (κ := WitParams κw κ0) (f := f) Γ)
            (Syntax.Henkin.mapParamsFormula (σ := σ) (f := f) χ) := by
        simpa [f, mapParamsContext, Syntax.Henkin.mapParamsFormula_substFormula] using ihDer
      exact DerivesWit.sigmaE (σ := σ) (κw := κw') (κ0 := κ0')
        (Γ := mapParamsContext (σ := σ) (κ := WitParams κw κ0) (f := f) Γ)
        (x := x) (a := a)
        (φ := Syntax.Henkin.mapParamsFormula (σ := σ) (f := f) φ)
        (χ := Syntax.Henkin.mapParamsFormula (σ := σ) (f := f) χ)
        hSigma' haΓ' haVars' haχ' ihDer'
  | sigmaE_wit hSigma hwΓ hwχ hDer ihSigma ihDer =>
      rename_i Γ x w φ χ
      have hwΓ' :
          (Sum.inl (fw w) : WitParams κw' κ0') ∉
            paramsContext (σ := σ) (κ := WitParams κw' κ0')
              (mapParamsContext (σ := σ) (κ := WitParams κw κ0) (f := f) Γ) := by
        -- `paramsContext (mapParamsContext f Γ) = (paramsContext Γ).image f`.
        simpa [f] using
          (hFreshImage
            (S := paramsContext (σ := σ) (κ := WitParams κw κ0) Γ)
            (w := w) hwΓ)
      have hwχ' :
          (Sum.inl (fw w) : WitParams κw' κ0') ∉
            Syntax.Henkin.paramsFormula (σ := σ) (κ := WitParams κw' κ0')
              (Syntax.Henkin.mapParamsFormula (σ := σ) (f := f) χ) := by
        simpa [f] using
          (hFreshImage
            (S := Syntax.Henkin.paramsFormula (σ := σ) (κ := WitParams κw κ0) χ)
            (w := w) hwχ)
      have hBodyEq :
          Syntax.Henkin.mapParamsFormula (σ := σ) (f := f)
              (Syntax.Henkin.witnessBodyW (σ := σ) (κw := κw) (κ := κ0) x w φ) =
            Syntax.Henkin.witnessBodyW (σ := σ) (κw := κw') (κ := κ0') x (fw w)
              (Syntax.Henkin.mapParamsFormula (σ := σ) (f := f) φ) := by
        simp [f, Syntax.Henkin.witnessBodyW, Syntax.Henkin.witTerm,
          Syntax.Henkin.mapParamsFormula_substFormula, Syntax.Henkin.mapParamsTerm]
      have hSigma' :
          DerivesWit (σ := σ) (κw := κw') (κ0 := κ0')
            (mapParamsContext (σ := σ) (κ := WitParams κw κ0) (f := f) Γ)
            (.sigma x (Syntax.Henkin.mapParamsFormula (σ := σ) (f := f) φ)) := by
        simpa [f] using ihSigma
      refine DerivesWit.sigmaE_wit (σ := σ) (κw := κw') (κ0 := κ0')
        (Γ := mapParamsContext (σ := σ) (κ := WitParams κw κ0) (f := f) Γ)
        (x := x) (w := fw w)
        (φ := Syntax.Henkin.mapParamsFormula (σ := σ) (f := f) φ)
        (χ := Syntax.Henkin.mapParamsFormula (σ := σ) (f := f) χ)
        hSigma' hwΓ' hwχ' ?_
      -- Rewrite the head formula in the mapped premise context.
      simpa [f, mapParamsContext, hBodyEq] using ihDer
  | wk h hSub ih =>
      rename_i Γ Δ φ
      refine DerivesWit.wk ih ?_
      intro ψ hψ
      rcases List.mem_map.1 hψ with ⟨θ, hθ, rfl⟩
      exact List.mem_map.2 ⟨θ, hSub hθ, rfl⟩

end DerivesWit

end

end NDH
end Noneism
end HeytingLean
