import HeytingLean.Noneism.Syntax.Subst

namespace HeytingLean
namespace Noneism
namespace Syntax
namespace Henkin

open Formula

universe u v

/-- Terms with both variables and Henkin parameters. -/
inductive TermH (κ : Type u) : Type u where
  | var (x : Var)
  | param (k : κ)
deriving DecidableEq, Repr

/-- First-order formulas over predicate symbols `σ` and Henkin parameters `κ`. -/
inductive FormulaH (σ : Type) (κ : Type u) : Type u where
  | top
  | bot
  | pred (p : σ) (args : List (TermH κ))
  | eExists (t : TermH κ)
  | not (φ : FormulaH σ κ)
  | and (φ ψ : FormulaH σ κ)
  | or  (φ ψ : FormulaH σ κ)
  | imp (φ ψ : FormulaH σ κ)
  | sigma (x : Var) (φ : FormulaH σ κ)
  | pi    (x : Var) (φ : FormulaH σ κ)
deriving DecidableEq, Repr

/-- Free variables of a Henkin term. Parameters are not free variables. -/
def fvTerm {κ : Type u} : TermH κ → Finset Var
  | .var x => {x}
  | .param _ => ∅

/-- Henkin parameters appearing in a term. Variables contribute no parameters. -/
def paramsTerm {κ : Type u} [DecidableEq κ] : TermH κ → Finset κ
  | .var _ => ∅
  | .param k => {k}

@[simp] theorem paramsTerm_var {κ : Type u} [DecidableEq κ] (x : Var) :
    paramsTerm (.var x : TermH κ) = ∅ := rfl

@[simp] theorem paramsTerm_param {κ : Type u} [DecidableEq κ] (k : κ) :
    paramsTerm (.param k : TermH κ) = {k} := rfl

/-- Free variables of a list of Henkin terms. -/
def fvTerms {κ : Type u} (ts : List (TermH κ)) : Finset Var :=
  ts.foldr (fun t acc => fvTerm t ∪ acc) ∅

@[simp] theorem fvTerms_nil {κ : Type u} :
    fvTerms (κ := κ) ([] : List (TermH κ)) = ∅ := rfl

@[simp] theorem fvTerms_cons {κ : Type u} (t : TermH κ) (ts : List (TermH κ)) :
    fvTerms (κ := κ) (t :: ts) = fvTerm t ∪ fvTerms (κ := κ) ts := by
  simp [fvTerms]

/-- Henkin parameters appearing in a list of terms. -/
def paramsTerms {κ : Type u} [DecidableEq κ] (ts : List (TermH κ)) : Finset κ :=
  ts.foldr (fun t acc => paramsTerm t ∪ acc) ∅

@[simp] theorem paramsTerms_nil {κ : Type u} [DecidableEq κ] :
    paramsTerms (κ := κ) ([] : List (TermH κ)) = ∅ := rfl

@[simp] theorem paramsTerms_cons {κ : Type u} [DecidableEq κ] (t : TermH κ) (ts : List (TermH κ)) :
    paramsTerms (κ := κ) (t :: ts) = paramsTerm t ∪ paramsTerms (κ := κ) ts := by
  simp [paramsTerms]

/-- Free variables of a Henkin formula. -/
def fvFormula {σ : Type} {κ : Type u} : FormulaH σ κ → Finset Var
  | .top => ∅
  | .bot => ∅
  | .pred _ args => fvTerms args
  | .eExists t => fvTerm t
  | .not φ => fvFormula φ
  | .and φ ψ => fvFormula φ ∪ fvFormula ψ
  | .or φ ψ => fvFormula φ ∪ fvFormula ψ
  | .imp φ ψ => fvFormula φ ∪ fvFormula ψ
  | .sigma x φ => (fvFormula φ).erase x
  | .pi x φ => (fvFormula φ).erase x

/-- Henkin parameters appearing in a formula. -/
def paramsFormula {σ : Type} {κ : Type u} [DecidableEq κ] : FormulaH σ κ → Finset κ
  | .top => ∅
  | .bot => ∅
  | .pred _ args => paramsTerms args
  | .eExists t => paramsTerm t
  | .not φ => paramsFormula φ
  | .and φ ψ => paramsFormula φ ∪ paramsFormula ψ
  | .or φ ψ => paramsFormula φ ∪ paramsFormula ψ
  | .imp φ ψ => paramsFormula φ ∪ paramsFormula ψ
  | .sigma _ φ => paramsFormula φ
  | .pi _ φ => paramsFormula φ

@[simp] theorem paramsFormula_top {σ : Type} {κ : Type u} [DecidableEq κ] :
    paramsFormula (σ := σ) (κ := κ) (.top : FormulaH σ κ) = ∅ := rfl

@[simp] theorem paramsFormula_bot {σ : Type} {κ : Type u} [DecidableEq κ] :
    paramsFormula (σ := σ) (κ := κ) (.bot : FormulaH σ κ) = ∅ := rfl

/-- Henkin parameters appearing in a Henkin-context (union over `paramsFormula`). -/
def paramsContext {σ : Type} {κ : Type u} [DecidableEq κ] (Γ : List (FormulaH σ κ)) : Finset κ :=
  Γ.foldr (fun φ acc => paramsFormula (σ := σ) (κ := κ) φ ∪ acc) ∅

@[simp] theorem paramsContext_nil {σ : Type} {κ : Type u} [DecidableEq κ] :
    paramsContext (σ := σ) (κ := κ) ([] : List (FormulaH σ κ)) = ∅ := rfl

@[simp] theorem paramsContext_cons {σ : Type} {κ : Type u} [DecidableEq κ]
    (φ : FormulaH σ κ) (Γ : List (FormulaH σ κ)) :
    paramsContext (σ := σ) (κ := κ) (φ :: Γ) =
      paramsFormula (σ := σ) (κ := κ) φ ∪ paramsContext (σ := σ) (κ := κ) Γ := by
  simp [paramsContext]

/-- Map Henkin parameters in a term. -/
def mapParamsTerm {κ : Type u} {κ' : Type v} (f : κ → κ') : TermH κ → TermH κ'
  | .var x => .var x
  | .param k => .param (f k)

/-- Map Henkin parameters in a list of terms. -/
def mapParamsTerms {κ : Type u} {κ' : Type v} (f : κ → κ') (ts : List (TermH κ)) : List (TermH κ') :=
  ts.map (mapParamsTerm f)

/-- Map Henkin parameters in a formula. -/
def mapParamsFormula {σ : Type} {κ : Type u} {κ' : Type v} (f : κ → κ') : FormulaH σ κ → FormulaH σ κ'
  | .top => .top
  | .bot => .bot
  | .pred p args => .pred p (mapParamsTerms f args)
  | .eExists t => .eExists (mapParamsTerm f t)
  | .not φ => .not (mapParamsFormula f φ)
  | .and φ ψ => .and (mapParamsFormula f φ) (mapParamsFormula f ψ)
  | .or φ ψ => .or (mapParamsFormula f φ) (mapParamsFormula f ψ)
  | .imp φ ψ => .imp (mapParamsFormula f φ) (mapParamsFormula f ψ)
  | .sigma x φ => .sigma x (mapParamsFormula f φ)
  | .pi x φ => .pi x (mapParamsFormula f φ)

/-! ### `params*` under parameter renaming -/

open scoped Classical

@[simp] theorem paramsTerm_mapParamsTerm
    {κ : Type u} {κ' : Type v} [DecidableEq κ] [DecidableEq κ']
    (f : κ → κ') (t : TermH κ) :
    paramsTerm (κ := κ') (mapParamsTerm f t) =
      (paramsTerm (κ := κ) t).image f := by
  cases t with
  | var x =>
      simp [paramsTerm, mapParamsTerm]
  | param k =>
      simp [paramsTerm, mapParamsTerm]

@[simp] theorem paramsTerms_mapParamsTerms
    {κ : Type u} {κ' : Type v} [DecidableEq κ] [DecidableEq κ']
    (f : κ → κ') (ts : List (TermH κ)) :
    paramsTerms (κ := κ') (mapParamsTerms f ts) =
      (paramsTerms (κ := κ) ts).image f := by
  induction ts with
  | nil =>
      simp [paramsTerms, mapParamsTerms]
  | cons t ts ih =>
      have ih' :
          paramsTerms (κ := κ') (List.map (mapParamsTerm f) ts) =
            (paramsTerms (κ := κ) ts).image f := by
        simpa [mapParamsTerms] using ih
      simp [mapParamsTerms, paramsTerms_cons, paramsTerm_mapParamsTerm, Finset.image_union, ih']

@[simp] theorem paramsFormula_mapParamsFormula
    {σ : Type} {κ : Type u} {κ' : Type v} [DecidableEq κ] [DecidableEq κ']
    (f : κ → κ') (φ : FormulaH σ κ) :
    paramsFormula (σ := σ) (κ := κ') (mapParamsFormula (σ := σ) f φ) =
      (paramsFormula (σ := σ) (κ := κ) φ).image f := by
  induction φ with
  | top =>
      simp [paramsFormula, mapParamsFormula]
  | bot =>
      simp [paramsFormula, mapParamsFormula]
  | pred p args =>
      simp [paramsFormula, mapParamsFormula, paramsTerms_mapParamsTerms]
  | eExists t =>
      simp [paramsFormula, mapParamsFormula, paramsTerm_mapParamsTerm]
  | not φ ih =>
      simp [paramsFormula, mapParamsFormula, ih]
  | and φ ψ ihφ ihψ =>
      simp [paramsFormula, mapParamsFormula, ihφ, ihψ, Finset.image_union]
  | or φ ψ ihφ ihψ =>
      simp [paramsFormula, mapParamsFormula, ihφ, ihψ, Finset.image_union]
  | imp φ ψ ihφ ihψ =>
      simp [paramsFormula, mapParamsFormula, ihφ, ihψ, Finset.image_union]
  | sigma x φ ih =>
      simp [paramsFormula, mapParamsFormula, ih]
  | pi x φ ih =>
      simp [paramsFormula, mapParamsFormula, ih]

@[simp] theorem paramsContext_mapParamsContext
    {σ : Type} {κ : Type u} {κ' : Type v} [DecidableEq κ] [DecidableEq κ']
    (f : κ → κ') (Γ : List (FormulaH σ κ)) :
    paramsContext (σ := σ) (κ := κ') (Γ.map (mapParamsFormula (σ := σ) f)) =
      (paramsContext (σ := σ) (κ := κ) Γ).image f := by
  induction Γ with
  | nil =>
      simp [paramsContext]
  | cons φ Γ ih =>
      -- Use the `cons` unfolding on both sides and the IH for the tail.
      simp [paramsContext_cons, paramsFormula_mapParamsFormula, ih, Finset.image_union]

@[simp] theorem fvTerm_mapParamsTerm {κ : Type u} {κ' : Type v} (f : κ → κ') (t : TermH κ) :
    fvTerm (mapParamsTerm f t) = fvTerm t := by
  cases t <;> rfl

@[simp] theorem fvTerms_mapParamsTerms {κ : Type u} {κ' : Type v} (f : κ → κ') (ts : List (TermH κ)) :
    fvTerms (κ := κ') (mapParamsTerms f ts) = fvTerms (κ := κ) ts := by
  induction ts with
  | nil =>
      rfl
  | cons t ts ih =>
      have ih' : fvTerms (κ := κ') (List.map (mapParamsTerm f) ts) = fvTerms (κ := κ) ts := by
        simpa [mapParamsTerms] using ih
      simp [mapParamsTerms, fvTerms_cons, fvTerm_mapParamsTerm, ih']

@[simp] theorem fvFormula_mapParamsFormula {σ : Type} {κ : Type u} {κ' : Type v}
    (f : κ → κ') (φ : FormulaH σ κ) :
    fvFormula (σ := σ) (κ := κ') (mapParamsFormula f φ) = fvFormula (σ := σ) (κ := κ) φ := by
  induction φ with
  | top => rfl
  | bot => rfl
  | pred p args =>
      simp [fvFormula, mapParamsFormula, fvTerms_mapParamsTerms]
  | eExists t =>
      simp [fvFormula, mapParamsFormula]
  | not φ ih =>
      simpa [fvFormula, mapParamsFormula] using ih
  | and φ ψ ihφ ihψ =>
      simp [fvFormula, mapParamsFormula, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
      simp [fvFormula, mapParamsFormula, ihφ, ihψ]
  | imp φ ψ ihφ ihψ =>
      simp [fvFormula, mapParamsFormula, ihφ, ihψ]
  | sigma x φ ih =>
      simp [fvFormula, mapParamsFormula, ih]
  | pi x φ ih =>
      simp [fvFormula, mapParamsFormula, ih]

@[simp] theorem mapParamsTerm_leftInverse
    {κ κ' : Type} {f : κ → κ'} {g : κ' → κ} (hfg : Function.LeftInverse g f) (t : TermH κ) :
    mapParamsTerm g (mapParamsTerm f t) = t := by
  cases t with
  | var x =>
      rfl
  | param k =>
      simpa [mapParamsTerm] using congrArg TermH.param (hfg k)

@[simp] theorem mapParamsTerms_leftInverse
    {κ κ' : Type} {f : κ → κ'} {g : κ' → κ} (hfg : Function.LeftInverse g f)
    (ts : List (TermH κ)) :
    mapParamsTerms g (mapParamsTerms f ts) = ts := by
  induction ts with
  | nil =>
      rfl
  | cons t ts ih =>
      have ih' : List.map (mapParamsTerm g ∘ mapParamsTerm f) ts = ts := by
        simpa [mapParamsTerms, List.map_map, Function.comp] using ih
      simp [mapParamsTerms, List.map_map,
        mapParamsTerm_leftInverse (f := f) (g := g) hfg, ih']

theorem mapParamsFormula_leftInverse
    {σ κ κ' : Type} {f : κ → κ'} {g : κ' → κ} (hfg : Function.LeftInverse g f)
    (φ : FormulaH σ κ) :
    mapParamsFormula (σ := σ) g (mapParamsFormula (σ := σ) f φ) = φ := by
  induction φ with
  | top => rfl
  | bot => rfl
  | pred p args =>
      simp [mapParamsFormula, mapParamsTerms_leftInverse, hfg]
  | eExists t =>
      cases t <;> simp [mapParamsFormula, mapParamsTerm_leftInverse, hfg]
  | not φ ih =>
      simpa [mapParamsFormula] using congrArg FormulaH.not ih
  | and φ ψ ihφ ihψ =>
      simp [mapParamsFormula, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
      simp [mapParamsFormula, ihφ, ihψ]
  | imp φ ψ ihφ ihψ =>
      simp [mapParamsFormula, ihφ, ihψ]
  | sigma x φ ih =>
      simp [mapParamsFormula, ih]
  | pi x φ ih =>
      simp [mapParamsFormula, ih]

/-- Rename variable `x` to `y` in a Henkin term. -/
def renameTerm {κ : Type u} (x y : Var) : TermH κ → TermH κ
  | .var z => if z = x then .var y else .var z
  | .param k => .param k

/-- Rename variable `x` to `y` in a list of Henkin terms. -/
def renameTerms {κ : Type u} (x y : Var) (ts : List (TermH κ)) : List (TermH κ) :=
  ts.map (renameTerm x y)

/-- Rename variable `x` to `y` in a Henkin formula. -/
def renameFormula {σ : Type} {κ : Type u} (x y : Var) : FormulaH σ κ → FormulaH σ κ
  | .top => .top
  | .bot => .bot
  | .pred p args => .pred p (renameTerms x y args)
  | .eExists t => .eExists (renameTerm x y t)
  | .not φ => .not (renameFormula x y φ)
  | .and φ ψ => .and (renameFormula x y φ) (renameFormula x y ψ)
  | .or φ ψ => .or (renameFormula x y φ) (renameFormula x y ψ)
  | .imp φ ψ => .imp (renameFormula x y φ) (renameFormula x y ψ)
  | .sigma z φ =>
      if z = x then .sigma y (renameFormula x y φ) else .sigma z (renameFormula x y φ)
  | .pi z φ =>
      if z = x then .pi y (renameFormula x y φ) else .pi z (renameFormula x y φ)

@[simp] theorem mapParamsTerm_renameTerm {κ : Type u} {κ' : Type v}
    (f : κ → κ') (x y : Var) (t : TermH κ) :
    mapParamsTerm f (renameTerm x y t) = renameTerm x y (mapParamsTerm f t) := by
  cases t with
  | var z =>
      by_cases hz : z = x <;> simp [renameTerm, mapParamsTerm, hz]
  | param k =>
      simp [renameTerm, mapParamsTerm]

@[simp] theorem mapParamsTerms_renameTerms {κ : Type u} {κ' : Type v} (f : κ → κ') (x y : Var)
    (ts : List (TermH κ)) :
    mapParamsTerms f (renameTerms x y ts) = renameTerms x y (mapParamsTerms f ts) := by
  simp [renameTerms, mapParamsTerms, List.map_map, mapParamsTerm_renameTerm]

@[simp] theorem mapParamsFormula_renameFormula {σ : Type} {κ : Type u} {κ' : Type v}
    (f : κ → κ') (x y : Var)
    (φ : FormulaH σ κ) :
    mapParamsFormula (σ := σ) f (renameFormula x y φ) =
      renameFormula x y (mapParamsFormula (σ := σ) f φ) := by
  induction φ with
  | top => rfl
  | bot => rfl
  | pred p args =>
      simp [renameFormula, mapParamsFormula, mapParamsTerms_renameTerms]
  | eExists t =>
      simp [renameFormula, mapParamsFormula, mapParamsTerm_renameTerm]
  | not φ ih =>
      simpa [renameFormula, mapParamsFormula] using congrArg FormulaH.not ih
  | and φ ψ ihφ ihψ =>
      simp [renameFormula, mapParamsFormula, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
      simp [renameFormula, mapParamsFormula, ihφ, ihψ]
  | imp φ ψ ihφ ihψ =>
      simp [renameFormula, mapParamsFormula, ihφ, ihψ]
  | sigma z φ ih =>
      by_cases hz : z = x <;> simp [renameFormula, mapParamsFormula, hz, ih]
  | pi z φ ih =>
      by_cases hz : z = x <;> simp [renameFormula, mapParamsFormula, hz, ih]

/-- Variables appearing anywhere in a Henkin formula (free or bound). -/
def varsFormula {σ : Type} {κ : Type u} : FormulaH σ κ → Finset Var
  | .top => ∅
  | .bot => ∅
  | .pred _ args => fvTerms args
  | .eExists t => fvTerm t
  | .not φ => varsFormula φ
  | .and φ ψ => varsFormula φ ∪ varsFormula ψ
  | .or φ ψ => varsFormula φ ∪ varsFormula ψ
  | .imp φ ψ => varsFormula φ ∪ varsFormula ψ
  | .sigma x φ => insert x (varsFormula φ)
  | .pi x φ => insert x (varsFormula φ)

@[simp] theorem varsFormula_mapParamsFormula {σ : Type} {κ : Type u} {κ' : Type v}
    (f : κ → κ') (φ : FormulaH σ κ) :
    varsFormula (σ := σ) (κ := κ') (mapParamsFormula (σ := σ) f φ) =
      varsFormula (σ := σ) (κ := κ) φ := by
  induction φ with
  | top => rfl
  | bot => rfl
  | pred p args =>
      -- `varsFormula` only sees variables; mapping parameters preserves `fvTerms`.
      simp [varsFormula, mapParamsFormula, fvTerms_mapParamsTerms]
  | eExists t =>
      simp [varsFormula, mapParamsFormula]
  | not φ ih =>
      simpa [varsFormula, mapParamsFormula] using ih
  | and φ ψ ihφ ihψ =>
      simp [varsFormula, mapParamsFormula, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
      simp [varsFormula, mapParamsFormula, ihφ, ihψ]
  | imp φ ψ ihφ ihψ =>
      simp [varsFormula, mapParamsFormula, ihφ, ihψ]
  | sigma x φ ih =>
      simp [varsFormula, mapParamsFormula, ih]
  | pi x φ ih =>
      simp [varsFormula, mapParamsFormula, ih]

/-- Bound variables of a Henkin formula. -/
def boundVars {σ : Type} {κ : Type u} : FormulaH σ κ → Finset Var
  | .top => ∅
  | .bot => ∅
  | .pred _ _ => ∅
  | .eExists _ => ∅
  | .not φ => boundVars φ
  | .and φ ψ => boundVars φ ∪ boundVars ψ
  | .or φ ψ => boundVars φ ∪ boundVars ψ
  | .imp φ ψ => boundVars φ ∪ boundVars ψ
  | .sigma x φ => insert x (boundVars φ)
  | .pi x φ => insert x (boundVars φ)

/-- Bound variables are among the variables appearing in the formula. -/
theorem boundVars_subset_varsFormula {σ : Type} {κ : Type u} :
    ∀ φ : FormulaH σ κ, boundVars (σ := σ) (κ := κ) φ ⊆ varsFormula (σ := σ) (κ := κ) φ := by
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
      simp [boundVars, varsFormula] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (ihφ hx)
      · exact Or.inr (ihψ hx)
  | or φ ψ ihφ ihψ =>
      intro x hx
      simp [boundVars, varsFormula] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (ihφ hx)
      · exact Or.inr (ihψ hx)
  | imp φ ψ ihφ ihψ =>
      intro x hx
      simp [boundVars, varsFormula] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (ihφ hx)
      · exact Or.inr (ihψ hx)
  | sigma x φ ih =>
      intro y hy
      simp [boundVars, varsFormula] at hy ⊢
      rcases hy with rfl | hy
      · exact Or.inl rfl
      · exact Or.inr (ih hy)
  | pi x φ ih =>
      intro y hy
      simp [boundVars, varsFormula] at hy ⊢
      rcases hy with rfl | hy
      · exact Or.inl rfl
      · exact Or.inr (ih hy)

theorem not_mem_boundVars_of_not_mem_varsFormula {σ : Type} {κ : Type u} {a : Var} {φ : FormulaH σ κ}
    (ha : a ∉ varsFormula (σ := σ) (κ := κ) φ) :
    a ∉ boundVars (σ := σ) (κ := κ) φ := by
  exact fun h => ha (boundVars_subset_varsFormula (σ := σ) (κ := κ) φ h)

/-- Formula size for well-founded recursion on Henkin formulas. -/
def fSize {σ : Type} {κ : Type u} : FormulaH σ κ → Nat
  | .top => 1
  | .bot => 1
  | .pred _ _ => 1
  | .eExists _ => 1
  | .not φ => fSize φ + 1
  | .and φ ψ => fSize φ + fSize ψ + 1
  | .or φ ψ => fSize φ + fSize ψ + 1
  | .imp φ ψ => fSize φ + fSize ψ + 1
  | .sigma _ φ => fSize φ + 1
  | .pi _ φ => fSize φ + 1

theorem fSize_renameFormula {σ : Type} {κ : Type u} (x y : Var) (φ : FormulaH σ κ) :
    fSize (renameFormula x y φ) = fSize φ := by
  induction φ with
  | top => simp [renameFormula, fSize]
  | bot => simp [renameFormula, fSize]
  | pred p args => simp [renameFormula, fSize]
  | eExists t => simp [renameFormula, fSize]
  | not φ ih => simpa [renameFormula, fSize] using congrArg Nat.succ ih
  | and φ ψ ihφ ihψ => simp [renameFormula, fSize, ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp [renameFormula, fSize, ihφ, ihψ]
  | imp φ ψ ihφ ihψ => simp [renameFormula, fSize, ihφ, ihψ]
  | sigma z φ ih =>
      by_cases hz : z = x <;> simp [renameFormula, fSize, hz, ih]
  | pi z φ ih =>
      by_cases hz : z = x <;> simp [renameFormula, fSize, hz, ih]

/-- Substitute variable `x` with term `s` in a Henkin term. -/
def substTerm {κ : Type u} (x : Var) (s : TermH κ) : TermH κ → TermH κ
  | .var z => if z = x then s else .var z
  | .param k => .param k

@[simp] theorem mapParamsTerm_substTerm {κ : Type u} {κ' : Type v}
    (f : κ → κ') (x : Var) (s : TermH κ)
    (t : TermH κ) :
    mapParamsTerm f (substTerm (κ := κ) x s t) =
      substTerm (κ := κ') x (mapParamsTerm f s) (mapParamsTerm f t) := by
  cases t with
  | var z =>
      by_cases hz : z = x <;> simp [substTerm, mapParamsTerm, hz]
  | param k =>
      simp [substTerm, mapParamsTerm]

/-- Substitute variable `x` with term `s` in a list of Henkin terms. -/
def substTerms {κ : Type u} (x : Var) (s : TermH κ) (ts : List (TermH κ)) : List (TermH κ) :=
  ts.map (substTerm x s)

@[simp] theorem mapParamsTerms_substTerms {κ : Type u} {κ' : Type v}
    (f : κ → κ') (x : Var) (s : TermH κ)
    (ts : List (TermH κ)) :
    mapParamsTerms f (substTerms (κ := κ) x s ts) =
      substTerms (κ := κ') x (mapParamsTerm f s) (mapParamsTerms f ts) := by
  simp [substTerms, mapParamsTerms, List.map_map, mapParamsTerm_substTerm, Function.comp]

/-- Capture-avoiding substitution on Henkin formulas. -/
@[irreducible] def substFormula {σ : Type} {κ : Type u} (x : Var) (s : TermH κ) :
    FormulaH σ κ → FormulaH σ κ
  | .top => .top
  | .bot => .bot
  | .pred p args => .pred p (substTerms x s args)
  | .eExists t => .eExists (substTerm x s t)
  | .not φ => .not (substFormula x s φ)
  | .and φ ψ => .and (substFormula x s φ) (substFormula x s ψ)
  | .or φ ψ => .or (substFormula x s φ) (substFormula x s ψ)
  | .imp φ ψ => .imp (substFormula x s φ) (substFormula x s ψ)
  | .sigma z φ =>
      if z = x then
        .sigma z φ
      else if z ∈ fvTerm s ∧ x ∈ fvFormula φ then
        let avoid : Finset Var := varsFormula φ ∪ fvTerm s ∪ ({x, z} : Finset Var)
        let z' : Var := freshVar avoid
        .sigma z' (substFormula x s (renameFormula z z' φ))
      else
        .sigma z (substFormula x s φ)
  | .pi z φ =>
      if z = x then
        .pi z φ
      else if z ∈ fvTerm s ∧ x ∈ fvFormula φ then
        let avoid : Finset Var := varsFormula φ ∪ fvTerm s ∪ ({x, z} : Finset Var)
        let z' : Var := freshVar avoid
        .pi z' (substFormula x s (renameFormula z z' φ))
      else
        .pi z (substFormula x s φ)
termination_by
  φ => fSize φ
decreasing_by
  all_goals
    simp [fSize, fSize_renameFormula]
    try omega

/--
Capture-avoiding substitution preserves `fSize`.

This is the key size fact used by completeness developments: substitution instances of the body of a
quantifier have strictly smaller `fSize` than the quantified formula itself.
-/
theorem fSize_substFormula {σ κ : Type} (x : Var) (s : TermH κ) :
    ∀ φ : FormulaH σ κ,
      fSize (substFormula (σ := σ) (κ := κ) x s φ) = fSize φ := by
  classical
  -- `substFormula` may recurse on `renameFormula z z' φ`, so structural induction is insufficient.
  have hwf : WellFounded (fun a b : FormulaH σ κ => fSize a < fSize b) :=
    (InvImage.wf (f := fun ψ : FormulaH σ κ => fSize ψ)
      (r := fun a b : Nat => a < b) Nat.lt_wfRel.wf)
  let C : FormulaH σ κ → Prop :=
    fun φ => fSize (substFormula (σ := σ) (κ := κ) x s φ) = fSize φ
  intro φ
  refine hwf.induction (C := C) φ ?_
  intro φ ih
  cases φ with
  | top =>
      simp [C, substFormula, fSize]
  | bot =>
      simp [C, substFormula, fSize]
  | pred p args =>
      simp [C, substFormula, fSize]
  | eExists t =>
      simp [C, substFormula, fSize]
  | not φ =>
      have ihφ := ih φ (by simp [fSize])
      simp [C, substFormula, fSize, ihφ]
  | and φ ψ =>
      have ihφ := ih φ (by simp [fSize, Nat.add_assoc])
      have ihψ :=
        ih ψ (by
          simpa [fSize, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (Nat.lt_add_of_pos_left (n := fSize ψ) (k := fSize φ + 1) (Nat.succ_pos _)))
      simp [C, substFormula, fSize, ihφ, ihψ]
  | or φ ψ =>
      have ihφ := ih φ (by simp [fSize, Nat.add_assoc])
      have ihψ :=
        ih ψ (by
          simpa [fSize, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (Nat.lt_add_of_pos_left (n := fSize ψ) (k := fSize φ + 1) (Nat.succ_pos _)))
      simp [C, substFormula, fSize, ihφ, ihψ]
  | imp φ ψ =>
      have ihφ := ih φ (by simp [fSize, Nat.add_assoc])
      have ihψ :=
        ih ψ (by
          simpa [fSize, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (Nat.lt_add_of_pos_left (n := fSize ψ) (k := fSize φ + 1) (Nat.succ_pos _)))
      simp [C, substFormula, fSize, ihφ, ihψ]
  | sigma z φ =>
      by_cases hzx : z = x
      · subst hzx
        simp [C, substFormula, fSize]
      · by_cases hcap : z ∈ fvTerm s ∧ x ∈ fvFormula (σ := σ) (κ := κ) φ
        ·
          -- Match the `simp` normal form of the `avoid` set used in `substFormula`.
          have ihRen :=
            ih (renameFormula z (freshVar (insert x (varsFormula (σ := σ) (κ := κ) φ ∪ fvTerm (κ := κ) s))) φ) (by
              simp [fSize, fSize_renameFormula])
          simp [C, substFormula, fSize, hzx, hcap, ihRen, fSize_renameFormula]
        ·
          have ihφ := ih φ (by simp [fSize])
          simp [C, substFormula, fSize, hzx, hcap, ihφ]
  | pi z φ =>
      by_cases hzx : z = x
      · subst hzx
        simp [C, substFormula, fSize]
      · by_cases hcap : z ∈ fvTerm s ∧ x ∈ fvFormula (σ := σ) (κ := κ) φ
        ·
          have ihRen :=
            ih (renameFormula z (freshVar (insert x (varsFormula (σ := σ) (κ := κ) φ ∪ fvTerm (κ := κ) s))) φ) (by
              simp [fSize, fSize_renameFormula])
          simp [C, substFormula, fSize, hzx, hcap, ihRen, fSize_renameFormula]
        ·
          have ihφ := ih φ (by simp [fSize])
          simp [C, substFormula, fSize, hzx, hcap, ihφ]

@[simp] theorem mapParamsFormula_substFormula
    {σ κ κ' : Type} (f : κ → κ') (x : Var) (s : TermH κ) (φ : FormulaH σ κ) :
    mapParamsFormula (σ := σ) f (substFormula (σ := σ) (κ := κ) x s φ) =
      substFormula (σ := σ) (κ := κ') x (mapParamsTerm f s) (mapParamsFormula (σ := σ) f φ) := by
  classical
  -- `substFormula` may recurse on `renameFormula z z' φ`, so structural induction is insufficient.
  have hwf : WellFounded (fun a b : FormulaH σ κ => fSize a < fSize b) :=
    (InvImage.wf (f := fun ψ : FormulaH σ κ => fSize ψ) (r := fun a b : Nat => a < b) Nat.lt_wfRel.wf)
  let C : FormulaH σ κ → Prop :=
    fun φ =>
      mapParamsFormula (σ := σ) f (substFormula (σ := σ) (κ := κ) x s φ) =
        substFormula (σ := σ) (κ := κ') x (mapParamsTerm f s) (mapParamsFormula (σ := σ) f φ)
  refine hwf.induction (C := C) φ ?_
  intro φ ih
  cases φ with
  | top =>
      simp [C, substFormula, mapParamsFormula]
  | bot =>
      simp [C, substFormula, mapParamsFormula]
  | pred p args =>
      simp [C, substFormula, mapParamsFormula, mapParamsTerms_substTerms]
  | eExists t =>
      simp [C, substFormula, mapParamsFormula, mapParamsTerm_substTerm]
  | not φ =>
      have ihφ := ih φ (by simp [fSize])
      simp [C, substFormula, mapParamsFormula, ihφ]
  | and φ ψ =>
      have ihφ := ih φ (by simp [fSize, Nat.add_assoc])
      have ihψ :=
        ih ψ (by
          simpa [fSize, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (Nat.lt_add_of_pos_left (n := fSize ψ) (k := fSize φ + 1) (Nat.succ_pos _)))
      simp [C, substFormula, mapParamsFormula, ihφ, ihψ]
  | or φ ψ =>
      have ihφ := ih φ (by simp [fSize, Nat.add_assoc])
      have ihψ :=
        ih ψ (by
          simpa [fSize, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (Nat.lt_add_of_pos_left (n := fSize ψ) (k := fSize φ + 1) (Nat.succ_pos _)))
      simp [C, substFormula, mapParamsFormula, ihφ, ihψ]
  | imp φ ψ =>
      have ihφ := ih φ (by simp [fSize, Nat.add_assoc])
      have ihψ :=
        ih ψ (by
          simpa [fSize, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (Nat.lt_add_of_pos_left (n := fSize ψ) (k := fSize φ + 1) (Nat.succ_pos _)))
      simp [C, substFormula, mapParamsFormula, ihφ, ihψ]
  | sigma z φ =>
      by_cases hzx : z = x
      · subst hzx
        simp [C, substFormula, mapParamsFormula]
      · by_cases hcap : z ∈ fvTerm s ∧ x ∈ fvFormula (σ := σ) (κ := κ) φ
        · have ihRen :=
            ih (renameFormula z (freshVar (insert x (varsFormula φ ∪ fvTerm s))) φ) (by
              simp [fSize, fSize_renameFormula])
          simp [C, substFormula, mapParamsFormula, hzx, hcap, ihRen,
            mapParamsFormula_renameFormula, varsFormula_mapParamsFormula, fvTerm_mapParamsTerm,
            fvFormula_mapParamsFormula]
        · have ihφ := ih φ (by simp [fSize])
          simp [C, substFormula, mapParamsFormula, hzx, hcap, ihφ,
            fvTerm_mapParamsTerm, fvFormula_mapParamsFormula]
  | pi z φ =>
      by_cases hzx : z = x
      · subst hzx
        simp [C, substFormula, mapParamsFormula]
      · by_cases hcap : z ∈ fvTerm s ∧ x ∈ fvFormula (σ := σ) (κ := κ) φ
        · have ihRen :=
            ih (renameFormula z (freshVar (insert x (varsFormula φ ∪ fvTerm s))) φ) (by
              simp [fSize, fSize_renameFormula])
          simp [C, substFormula, mapParamsFormula, hzx, hcap, ihRen,
            mapParamsFormula_renameFormula, varsFormula_mapParamsFormula, fvTerm_mapParamsTerm,
            fvFormula_mapParamsFormula]
        · have ihφ := ih φ (by simp [fSize])
          simp [C, substFormula, mapParamsFormula, hzx, hcap, ihφ,
            fvTerm_mapParamsTerm, fvFormula_mapParamsFormula]

/-- Body formula selected by a Henkin witness parameter. -/
def witnessBody {σ κ : Type} (x : Var) (k : κ) (φ : FormulaH σ κ) : FormulaH σ κ :=
  substFormula x (.param k) φ

/-- Henkin witness schema `(sigma x φ) -> φ[param k / x]`. -/
def henkinAxiom {σ κ : Type} (x : Var) (k : κ) (φ : FormulaH σ κ) : FormulaH σ κ :=
  .imp (.sigma x φ) (witnessBody x k φ)

/-- Set of all Henkin witness schemas generated by a witness-choice function. -/
def henkinAxiomSet {σ κ : Type}
    (choose : Var → FormulaH σ κ → κ) : Set (FormulaH σ κ) :=
  fun ψ => ∃ x φ, ψ = henkinAxiom x (choose x φ) φ

/-! ### Witness-parameter layer (Track J / M1)

This is a backwards-compatible way to introduce a dedicated "Henkin constant" namespace for
witnesses without changing the core `TermH`/`FormulaH` inductives.

The idea is: work in `κ := Sum κw κ`, and reserve the left injection (`Sum.inl`) for witness
constants, while the right injection (`Sum.inr`) carries any pre-existing parameter payload.

This lets later proof-theory layers (Track J / M2+) use witness *terms* that are not tied to
context variables, avoiding the open-context eigenvariable/freshness bottleneck.
-/

/-- Parameters split into witness-constants `κw` and ambient parameters `κ`. -/
abbrev WitParams (κw κ : Type u) : Type u := Sum κw κ

/-- Inject a witness-constant parameter as a term. -/
def witTerm {κw κ : Type u} (w : κw) : TermH (WitParams κw κ) :=
  .param (Sum.inl w)

/-- Inject an ambient parameter as a term. -/
def paramTerm {κw κ : Type u} (k : κ) : TermH (WitParams κw κ) :=
  .param (Sum.inr k)

@[simp] theorem fvTerm_witTerm {κw κ : Type u} (w : κw) :
    fvTerm (κ := WitParams κw κ) (witTerm (κw := κw) (κ := κ) w) = ∅ := rfl

@[simp] theorem fvTerm_paramTerm {κw κ : Type u} (k : κ) :
    fvTerm (κ := WitParams κw κ) (paramTerm (κw := κw) (κ := κ) k) = ∅ := rfl

@[simp] theorem paramsTerm_witTerm {κw κ : Type u} [DecidableEq κw] [DecidableEq κ]
    (w : κw) :
    paramsTerm (κ := WitParams κw κ) (witTerm (κw := κw) (κ := κ) w) = {Sum.inl w} := rfl

@[simp] theorem paramsTerm_paramTerm {κw κ : Type u} [DecidableEq κw] [DecidableEq κ]
    (k : κ) :
    paramsTerm (κ := WitParams κw κ) (paramTerm (κw := κw) (κ := κ) k) = {Sum.inr k} := rfl

/-- Witness-body using a witness-constant term. -/
def witnessBodyW {σ : Type} {κw κ : Type u}
    (x : Var) (w : κw) (φ : FormulaH σ (WitParams κw κ)) : FormulaH σ (WitParams κw κ) :=
  substFormula (σ := σ) (κ := WitParams κw κ) x (witTerm (κw := κw) (κ := κ) w) φ

/-- Henkin witness schema `(sigma x φ) -> φ[witTerm w / x]`. -/
def henkinAxiomW {σ : Type} {κw κ : Type u}
    (x : Var) (w : κw) (φ : FormulaH σ (WitParams κw κ)) : FormulaH σ (WitParams κw κ) :=
  .imp (.sigma x φ) (witnessBodyW (σ := σ) (κw := κw) (κ := κ) x w φ)

/-- Set of all Henkin witness schemas generated by a witness-choice function into the witness namespace. -/
def henkinAxiomSetW {σ : Type} {κw κ : Type u}
    (chooseW : Var → FormulaH σ (WitParams κw κ) → κw) : Set (FormulaH σ (WitParams κw κ)) :=
  fun ψ => ∃ x φ, ψ = henkinAxiomW (σ := σ) (κw := κw) (κ := κ) x (chooseW x φ) φ

/-! ### Witness-namespace parameter support helpers -/

open scoped Classical

noncomputable section

/--
Extract the witness-constant parameters (`Sum.inl`) from a finite set of split parameters.
-/
def witParamsFinset {κw κ0 : Type u} [DecidableEq κw]
    (S : Finset (WitParams κw κ0)) : Finset κw :=
  Finset.filterMap
    (fun k =>
      match k with
      | Sum.inl w => some w
      | Sum.inr _ => none)
    S
    (by
      intro a a' b hb hb'
      cases a <;> cases a'
      all_goals
        cases hb <;> cases hb' <;> rfl)

/--
Extract the ambient parameters (`Sum.inr`) from a finite set of split parameters.
-/
def ambParamsFinset {κw κ0 : Type u} [DecidableEq κ0]
    (S : Finset (WitParams κw κ0)) : Finset κ0 :=
  Finset.filterMap
    (fun k =>
      match k with
      | Sum.inl _ => none
      | Sum.inr a => some a)
    S
    (by
      intro a a' b hb hb'
      cases a <;> cases a'
      all_goals
        cases hb <;> cases hb' <;> rfl)

@[simp] theorem mem_witParamsFinset_iff {κw κ0 : Type u} [DecidableEq κw]
    {S : Finset (WitParams κw κ0)} {w : κw} :
    w ∈ witParamsFinset (κw := κw) (κ0 := κ0) S ↔ (Sum.inl w : WitParams κw κ0) ∈ S := by
  classical
  -- `Finset.mem_filterMap` expands membership in the filtered image.
  simp [witParamsFinset, Finset.mem_filterMap]

@[simp] theorem mem_ambParamsFinset_iff {κw κ0 : Type u} [DecidableEq κ0]
    {S : Finset (WitParams κw κ0)} {a : κ0} :
    a ∈ ambParamsFinset (κw := κw) (κ0 := κ0) S ↔ (Sum.inr a : WitParams κw κ0) ∈ S := by
  classical
  simp [ambParamsFinset, Finset.mem_filterMap]

/-- Witness-parameter support of a formula in the split-parameter language. -/
def witParamsFormula {σ : Type} {κw κ0 : Type u} [DecidableEq κw]
    (φ : FormulaH σ (WitParams κw κ0)) : Finset κw :=
  witParamsFinset (κw := κw) (κ0 := κ0) (paramsFormula (σ := σ) (κ := WitParams κw κ0) φ)

/-- Witness-parameter support of a context in the split-parameter language. -/
def witParamsContext {σ : Type} {κw κ0 : Type u} [DecidableEq κw]
    (Γ : List (FormulaH σ (WitParams κw κ0))) : Finset κw :=
  witParamsFinset (κw := κw) (κ0 := κ0) (paramsContext (σ := σ) (κ := WitParams κw κ0) Γ)

end

/-- Embed original terms into the Henkin-term language. -/
def liftTerm {κ : Type} : Term → TermH κ
  | .var x => .var x

/-- Embed original formulas into the Henkin-formula language. -/
def liftFormula {σ κ : Type} : Formula σ → FormulaH σ κ
  | .top => .top
  | .bot => .bot
  | .pred p args => .pred p (args.map liftTerm)
  | .eExists t => .eExists (liftTerm t)
  | .not φ => .not (liftFormula φ)
  | .and φ ψ => .and (liftFormula φ) (liftFormula ψ)
  | .or φ ψ => .or (liftFormula φ) (liftFormula ψ)
  | .imp φ ψ => .imp (liftFormula φ) (liftFormula ψ)
  | .sigma x φ => .sigma x (liftFormula φ)
  | .pi x φ => .pi x (liftFormula φ)

@[simp] theorem fvTerm_param {κ : Type} (k : κ) :
    fvTerm (.param k : TermH κ) = ∅ := rfl

@[simp] theorem fvTerm_liftTerm {κ : Type} (t : Term) :
    fvTerm (liftTerm (κ := κ) t) = Syntax.fvTerm t := by
  cases t with
  | var => rfl

@[simp] theorem liftTerm_renameTerm {κ : Type} (x y : Var) (t : Term) :
    liftTerm (κ := κ) (Syntax.renameTerm x y t) =
      renameTerm x y (liftTerm (κ := κ) t) := by
  cases t with
  | var z =>
      by_cases hz : z = x
      · simp [Syntax.renameTerm, renameTerm, hz, liftTerm]
      · simp [Syntax.renameTerm, renameTerm, hz, liftTerm]

@[simp] theorem liftFormula_renameFormula {σ κ : Type} (x y : Var) (φ : Formula σ) :
    liftFormula (σ := σ) (κ := κ) (Syntax.renameFormula (σ := σ) x y φ) =
      renameFormula x y (liftFormula (σ := σ) (κ := κ) φ) := by
  induction φ with
  | top => rfl
  | bot => rfl
  | pred p args =>
      simp [Syntax.renameFormula, renameFormula, liftFormula, Syntax.renameTerms, renameTerms,
        List.map_map, Function.comp, liftTerm_renameTerm]
  | eExists t =>
      simp [Syntax.renameFormula, renameFormula, liftFormula, liftTerm_renameTerm]
  | not φ ih =>
      simpa [Syntax.renameFormula, renameFormula, liftFormula] using congrArg FormulaH.not ih
  | and φ ψ ihφ ihψ =>
      simp [Syntax.renameFormula, renameFormula, liftFormula, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
      simp [Syntax.renameFormula, renameFormula, liftFormula, ihφ, ihψ]
  | imp φ ψ ihφ ihψ =>
      simp [Syntax.renameFormula, renameFormula, liftFormula, ihφ, ihψ]
  | sigma z φ ih =>
      by_cases hz : z = x
      · simp [Syntax.renameFormula, renameFormula, liftFormula, hz, ih]
      · simp [Syntax.renameFormula, renameFormula, liftFormula, hz, ih]
  | pi z φ ih =>
      by_cases hz : z = x
      · simp [Syntax.renameFormula, renameFormula, liftFormula, hz, ih]
      · simp [Syntax.renameFormula, renameFormula, liftFormula, hz, ih]

@[simp] theorem liftTerm_substTerm_var {κ : Type} (x a : Var) (t : Term) :
    liftTerm (κ := κ) (Syntax.substTerm x (.var a) t) =
      substTerm x (.var a) (liftTerm (κ := κ) t) := by
  cases t with
  | var z =>
      by_cases hz : z = x
      · simp [Syntax.substTerm, substTerm, hz, liftTerm]
      · simp [Syntax.substTerm, substTerm, hz, liftTerm]

@[simp] theorem liftTerms_substTerms_var {κ : Type} (x a : Var) (ts : List Term) :
    (ts.map (liftTerm (κ := κ))).map (substTerm x (.var a)) =
      ts.map (liftTerm (κ := κ) ∘ Syntax.substTerm x (.var a)) := by
  induction ts with
  | nil =>
      simp
  | cons t ts ih =>
      simp [ih, liftTerm_substTerm_var]

@[simp] theorem fvTerms_liftTerms {κ : Type} (ts : List Term) :
    fvTerms (ts.map (liftTerm (κ := κ))) = Syntax.fvTerms ts := by
  induction ts with
  | nil =>
      simp [fvTerms, Syntax.fvTerms]
  | cons t ts ih =>
      simpa [fvTerms, Syntax.fvTerms, ih] using
        congrArg (fun u => Syntax.fvTerm t ∪ u) ih

@[simp] theorem fvFormula_liftFormula {σ κ : Type} (φ : Formula σ) :
    fvFormula (liftFormula (σ := σ) (κ := κ) φ) = Syntax.fvFormula (σ := σ) φ := by
  induction φ with
  | top => rfl
  | bot => rfl
  | pred p args =>
      calc
        fvFormula (liftFormula (σ := σ) (κ := κ) (.pred p args))
            = fvTerms (args.map (liftTerm (κ := κ))) := by rfl
        _ = Syntax.fvTerms args := fvTerms_liftTerms (κ := κ) args
        _ = Syntax.fvFormula (σ := σ) (.pred p args) := by rfl
  | eExists t =>
      simp [liftFormula, fvFormula, Syntax.fvFormula, fvTerm_liftTerm]
  | not φ ih =>
      simpa [liftFormula, fvFormula, Syntax.fvFormula] using ih
  | and φ ψ ihφ ihψ =>
      simp [liftFormula, fvFormula, Syntax.fvFormula, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
      simp [liftFormula, fvFormula, Syntax.fvFormula, ihφ, ihψ]
  | imp φ ψ ihφ ihψ =>
      simp [liftFormula, fvFormula, Syntax.fvFormula, ihφ, ihψ]
  | sigma x φ ih =>
      simp [liftFormula, fvFormula, Syntax.fvFormula, ih]
  | pi x φ ih =>
      simp [liftFormula, fvFormula, Syntax.fvFormula, ih]

@[simp] theorem varsFormula_liftFormula {σ κ : Type} (φ : Formula σ) :
    varsFormula (liftFormula (σ := σ) (κ := κ) φ) = Syntax.varsFormula (σ := σ) φ := by
  induction φ with
  | top => rfl
  | bot => rfl
  | pred p args =>
      calc
        varsFormula (liftFormula (σ := σ) (κ := κ) (.pred p args))
            = fvTerms (args.map (liftTerm (κ := κ))) := by rfl
        _ = Syntax.fvTerms args := fvTerms_liftTerms (κ := κ) args
        _ = Syntax.varsFormula (σ := σ) (.pred p args) := by rfl
  | eExists t =>
      simp [liftFormula, varsFormula, Syntax.varsFormula, fvTerm_liftTerm]
  | not φ ih =>
      simpa [liftFormula, varsFormula, Syntax.varsFormula] using ih
  | and φ ψ ihφ ihψ =>
      simp [liftFormula, varsFormula, Syntax.varsFormula, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
      simp [liftFormula, varsFormula, Syntax.varsFormula, ihφ, ihψ]
  | imp φ ψ ihφ ihψ =>
      simp [liftFormula, varsFormula, Syntax.varsFormula, ihφ, ihψ]
  | sigma x φ ih =>
      simp [liftFormula, varsFormula, Syntax.varsFormula, ih]
  | pi x φ ih =>
      simp [liftFormula, varsFormula, Syntax.varsFormula, ih]

@[simp] theorem boundVars_liftFormula {σ κ : Type} (φ : Formula σ) :
    boundVars (liftFormula (σ := σ) (κ := κ) φ) = Syntax.boundVars (σ := σ) φ := by
  induction φ with
  | top => rfl
  | bot => rfl
  | pred p args => rfl
  | eExists t => rfl
  | not φ ih =>
      simpa [liftFormula, boundVars, Syntax.boundVars] using ih
  | and φ ψ ihφ ihψ =>
      simp [liftFormula, boundVars, Syntax.boundVars, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
      simp [liftFormula, boundVars, Syntax.boundVars, ihφ, ihψ]
  | imp φ ψ ihφ ihψ =>
      simp [liftFormula, boundVars, Syntax.boundVars, ihφ, ihψ]
  | sigma x φ ih =>
      simp [liftFormula, boundVars, Syntax.boundVars, ih]
  | pi x φ ih =>
      simp [liftFormula, boundVars, Syntax.boundVars, ih]

end Henkin
end Syntax
end Noneism
end HeytingLean
