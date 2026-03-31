import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.W.Cardinal
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Order
import HeytingLean.Noneism.Syntax.Henkin

namespace HeytingLean
namespace Noneism
namespace HenkinCardinalBounds

open Syntax.Henkin

open scoped Classical

/-!
Cardinality bounds for the Henkin syntax `TermH` / `FormulaH`.

Purpose: support “assumption-free” Henkin-style constructions where we need a parameter type large
enough to index fresh witnesses without assuming `Encodable`.

Key move: present `FormulaH σ κ` as the image of a finitely-branching `WType` whose label type only
mentions the non-recursive payloads `σ`, `Var`, `TermH κ`, and `List (TermH κ)`.
Then use `WType.cardinalMk_le_max_aleph0_of_finite'`.
-/

namespace WEnc

/-- Labels for a `WType` presenting the shape of `FormulaH`. -/
inductive FLabel (σ : Type) (κ : Type) : Type where
  | top
  | bot
  | pred (p : σ) (args : List (TermH κ))
  | eExists (t : TermH κ)
  | not
  | and
  | or
  | imp
  | sigma (x : Var)
  | pi (x : Var)

/-- Finite arity for each label. -/
def FArity {σ : Type} {κ : Type} : FLabel σ κ → Type
  | .top => Empty
  | .bot => Empty
  | .pred _ _ => Empty
  | .eExists _ => Empty
  | .not => PUnit
  | .and => Bool
  | .or => Bool
  | .imp => Bool
  | .sigma _ => PUnit
  | .pi _ => PUnit

instance {σ : Type} {κ : Type} (a : FLabel σ κ) : Finite (FArity (σ := σ) (κ := κ) a) := by
  cases a <;> dsimp [FArity] <;> infer_instance

/-- Decode a `WType` tree into a Henkin formula. -/
def toFormula {σ : Type} {κ : Type} : WType (FArity (σ := σ) (κ := κ)) → FormulaH σ κ
  | ⟨.top, _⟩ => .top
  | ⟨.bot, _⟩ => .bot
  | ⟨.pred p args, _⟩ => .pred p args
  | ⟨.eExists t, _⟩ => .eExists t
  | ⟨.not, f⟩ => .not (toFormula (f ⟨⟩))
  | ⟨.and, f⟩ => .and (toFormula (f false)) (toFormula (f true))
  | ⟨.or, f⟩ => .or (toFormula (f false)) (toFormula (f true))
  | ⟨.imp, f⟩ => .imp (toFormula (f false)) (toFormula (f true))
  | ⟨.sigma x, f⟩ => .sigma x (toFormula (f ⟨⟩))
  | ⟨.pi x, f⟩ => .pi x (toFormula (f ⟨⟩))

/-- Encode a Henkin formula as a `WType` tree (structural recursion). -/
def ofFormula {σ : Type} {κ : Type} : FormulaH σ κ → WType (FArity (σ := σ) (κ := κ))
  | .top => ⟨.top, Empty.rec⟩
  | .bot => ⟨.bot, Empty.rec⟩
  | .pred p args => ⟨.pred p args, Empty.rec⟩
  | .eExists t => ⟨.eExists t, Empty.rec⟩
  | .not φ => ⟨.not, fun _ => ofFormula φ⟩
  | .and φ ψ => ⟨.and, fun b => Bool.rec (ofFormula φ) (ofFormula ψ) b⟩
  | .or φ ψ => ⟨.or, fun b => Bool.rec (ofFormula φ) (ofFormula ψ) b⟩
  | .imp φ ψ => ⟨.imp, fun b => Bool.rec (ofFormula φ) (ofFormula ψ) b⟩
  | .sigma x φ => ⟨.sigma x, fun _ => ofFormula φ⟩
  | .pi x φ => ⟨.pi x, fun _ => ofFormula φ⟩

@[simp] theorem toFormula_ofFormula {σ : Type} {κ : Type} (φ : FormulaH σ κ) :
    toFormula (σ := σ) (κ := κ) (ofFormula (σ := σ) (κ := κ) φ) = φ := by
  induction φ with
  | top => rfl
  | bot => rfl
  | pred p args => rfl
  | eExists t => rfl
  | not φ ih => simp [ofFormula, toFormula, ih]
  | and φ ψ ihφ ihψ =>
      simp [ofFormula, toFormula, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
      simp [ofFormula, toFormula, ihφ, ihψ]
  | imp φ ψ ihφ ihψ =>
      simp [ofFormula, toFormula, ihφ, ihψ]
  | sigma x φ ih =>
      simp [ofFormula, toFormula, ih]
  | pi x φ ih =>
      simp [ofFormula, toFormula, ih]

theorem toFormula_surjective {σ : Type} {κ : Type} :
    Function.Surjective (toFormula (σ := σ) (κ := κ)) := by
  intro φ
  refine ⟨ofFormula (σ := σ) (κ := κ) φ, ?_⟩
  simp

end WEnc

open Cardinal

/-! ### Helper bounds for `TermH` and lists -/

theorem mk_TermH_le_max (κ : Type) :
    #(TermH κ) ≤ max (#κ) Cardinal.aleph0 := by
  classical
  -- `TermH κ ≃ Var ⊕ κ`, and `#Var = ℵ₀`.
  have e : TermH κ ≃ Sum Var κ := by
    refine
      { toFun := fun t =>
          match t with
          | .var x => Sum.inl x
          | .param k => Sum.inr k
        invFun := fun s =>
          match s with
          | Sum.inl x => .var x
          | Sum.inr k => .param k
        left_inv := by intro t; cases t <;> rfl
        right_inv := by intro s; cases s <;> rfl }
  have : #(TermH κ) = #(Sum Var κ) := mk_congr e
  -- `#(Var ⊕ κ) = #Var + #κ ≤ max (max #Var #κ) ℵ₀ = max #κ ℵ₀`.
  have hsum : #(Sum Var κ) ≤ max (#κ) Cardinal.aleph0 := by
    have h : (#Var + #κ) ≤ max (max (#Var) (#κ)) Cardinal.aleph0 :=
      Cardinal.add_le_max (#Var) (#κ)
    -- Rewrite `#Var` to `ℵ₀`.
    simpa [Cardinal.mk_sum, Var, Cardinal.mk_nat, max_assoc, max_left_comm, max_comm] using h
  simpa [this] using hsum

theorem mk_list_TermH_le_max (κ : Type) :
    #(List (TermH κ)) ≤ max (#κ) Cardinal.aleph0 := by
  classical
  have hTerm : #(TermH κ) ≤ max (#κ) Cardinal.aleph0 := mk_TermH_le_max (κ := κ)
  -- `#(List α) = max #α ℵ₀`.
  letI : Nonempty (TermH κ) := ⟨.var 0⟩
  calc
    #(List (TermH κ)) = max (#(TermH κ)) Cardinal.aleph0 := by
      simpa using (Cardinal.mk_list_eq_max_mk_aleph0 (TermH κ))
    _ ≤ max (max (#κ) Cardinal.aleph0) Cardinal.aleph0 := by
      exact max_le_max hTerm le_rfl
    _ = max (#κ) Cardinal.aleph0 := by
      simp

/-! ### Main bound for `FormulaH` -/

theorem mk_FormulaH_le_max (σ : Type) (κ : Type) :
    #(FormulaH σ κ) ≤ max (#σ) (max (#κ) Cardinal.aleph0) := by
  classical
  -- Surjection from a finitely-branching `WType` to `FormulaH σ κ`.
  have hsurj :
      Function.Surjective (WEnc.toFormula (σ := σ) (κ := κ)) :=
    WEnc.toFormula_surjective (σ := σ) (κ := κ)
  have hmk_le_w :
      #(FormulaH σ κ) ≤ #(WType (WEnc.FArity (σ := σ) (κ := κ))) :=
    Cardinal.mk_le_of_surjective hsurj

  -- `WType` bound: `#WType ≤ max (lift #labels) ℵ₀`.
  have hW :
      #(WType (WEnc.FArity (σ := σ) (κ := κ))) ≤
        max (#(WEnc.FLabel σ κ)) Cardinal.aleph0 := by
    simpa using
      (WType.cardinalMk_le_max_aleph0_of_finite (α := WEnc.FLabel σ κ)
        (β := WEnc.FArity (σ := σ) (κ := κ)))

  -- Bound the label type by a simple tagged sum of payload types.
  let Dom : Type :=
    Sum (Fin 6)
      (Sum (σ × List (TermH κ))
        (Sum (TermH κ) (Sum Var Var)))

  have embLabel : WEnc.FLabel σ κ ↪ Dom := by
    classical
    refine ⟨fun a => ?_, ?_⟩
    · cases a with
      | top => exact Sum.inl ⟨0, by decide⟩
      | bot => exact Sum.inl ⟨1, by decide⟩
      | not => exact Sum.inl ⟨2, by decide⟩
      | and => exact Sum.inl ⟨3, by decide⟩
      | or => exact Sum.inl ⟨4, by decide⟩
      | imp => exact Sum.inl ⟨5, by decide⟩
      | pred p args => exact Sum.inr (Sum.inl (p, args))
      | eExists t => exact Sum.inr (Sum.inr (Sum.inl t))
      | sigma x => exact Sum.inr (Sum.inr (Sum.inr (Sum.inl x)))
      | pi x => exact Sum.inr (Sum.inr (Sum.inr (Sum.inr x)))
    · intro a b hab
      cases a <;> cases b <;> cases hab <;> rfl

  have hLabel_le_Dom : #(WEnc.FLabel σ κ) ≤ #Dom :=
    Cardinal.mk_le_of_injective embLabel.injective

  -- Now bound `#Dom` by `c := max (lift #σ) (max #κ ℵ₀)`.
  let c : Cardinal := max (#σ) (max (#κ) Cardinal.aleph0)
  have hc : Cardinal.aleph0 ≤ c := by
    -- `ℵ₀ ≤ max (#κ) ℵ₀ ≤ c`.
    exact le_trans (le_max_right (#κ) Cardinal.aleph0) (le_max_right _ _)

  have hFin : #(Fin 6) ≤ c := by
    have : #(Fin 6) < Cardinal.aleph0 := lt_aleph0_of_finite (Fin 6)
    exact this.le.trans hc

  have hTerm : #(TermH κ) ≤ c :=
    (mk_TermH_le_max (κ := κ)).trans (le_max_right _ _)

  have hList : #(List (TermH κ)) ≤ c :=
    (mk_list_TermH_le_max (κ := κ)).trans (le_max_right _ _)

  have hVar : #Var ≤ c := by
    -- `#Var = ℵ₀`.
    simpa [Var, Cardinal.mk_nat] using hc

  have hSumVar : #(Sum Var Var) ≤ c := by
    -- `#(Var ⊕ Var) = ℵ₀ + ℵ₀ ≤ c`.
    have h : #Var + #Var ≤ c := Cardinal.add_le_of_le hc hVar hVar
    simpa [Cardinal.mk_sum] using h

  have hProd : #(σ × List (TermH κ)) ≤ c := by
    -- `#(σ × L) = #σ * #L ≤ c` since `#σ ≤ c`, `#L ≤ c`, and `c` is infinite.
    have hσ : #σ ≤ c := le_max_left _ _
    have hmul : (#σ) * #(List (TermH κ)) ≤ max (max (#σ) (#(List (TermH κ)))) Cardinal.aleph0 :=
      Cardinal.mul_le_max _ _
    have hmax : max (max (#σ) (#(List (TermH κ)))) Cardinal.aleph0 ≤ c := by
      refine max_le ?_ hc
      exact max_le hσ hList
    simpa [Cardinal.mk_prod] using hmul.trans hmax

  have hDom_le_c : #Dom ≤ c := by
    -- Bound nested sums step-by-step using `Cardinal.add_le_of_le`.
    -- `#Dom = #Fin6 + (#(σ×List) + (#Term + #(Var⊕Var)))`.
    have h1 : #(Sum (Fin 6) (Sum (σ × List (TermH κ)) (Sum (TermH κ) (Sum Var Var)))) ≤ c := by
      -- `#(A ⊕ B) = #A + #B`.
      -- First show the right summand is ≤ c.
      have hRight : #(Sum (σ × List (TermH κ)) (Sum (TermH κ) (Sum Var Var))) ≤ c := by
        have hRight' : #(σ × List (TermH κ)) + #(Sum (TermH κ) (Sum Var Var)) ≤ c := by
          -- Need `#(Sum (TermH κ) (Sum Var Var)) ≤ c`.
          have hInner : #(Sum (TermH κ) (Sum Var Var)) ≤ c := by
            have hInner' : #(TermH κ) + #(Sum Var Var) ≤ c :=
              Cardinal.add_le_of_le hc hTerm hSumVar
            simpa [Cardinal.mk_sum] using hInner'
          exact Cardinal.add_le_of_le hc hProd hInner
        simpa [Cardinal.mk_sum] using hRight'
      have hAll : #(Fin 6) + #(Sum (σ × List (TermH κ)) (Sum (TermH κ) (Sum Var Var))) ≤ c :=
        Cardinal.add_le_of_le hc hFin hRight
      simpa [Cardinal.mk_sum] using hAll
    simpa [Dom] using h1

  have hLabel_le_c : #(WEnc.FLabel σ κ) ≤ c :=
    hLabel_le_Dom.trans hDom_le_c

  -- Combine all inequalities.
  -- `#FormulaH ≤ #WType ≤ max (lift #labels) ℵ₀ ≤ max c ℵ₀ = c`.
  have : #(FormulaH σ κ) ≤ max c Cardinal.aleph0 := by
    exact hmk_le_w.trans (hW.trans (max_le_max hLabel_le_c le_rfl))
  -- `max c ℵ₀ = c` since `ℵ₀ ≤ c`.
  simpa [c, max_eq_left hc] using this

/-! ### A “Big Enough” Parameter Type Without `Encodable` -/

/--
A convenient `Type`-level parameter namespace that is always infinite and at least as large as `σ`:
`κ := σ ⊕ Nat`.

This is useful when you want a canonical “fresh witness supply” without adding any countability
assumptions on `σ`.
-/
abbrev BigKappa (σ : Type) : Type := Sum σ Nat

theorem mk_BigKappa (σ : Type) : #(BigKappa σ) = max (#σ) Cardinal.aleph0 := by
  -- `#(σ ⊕ Nat) = #σ + ℵ₀ = ℵ₀ + #σ = max ℵ₀ #σ = max #σ ℵ₀`.
  calc
    #(BigKappa σ) = #σ + Cardinal.aleph0 := by
      simp [BigKappa, Cardinal.mk_sum]
    _ = Cardinal.aleph0 + #σ := by
      simp [add_comm]
    _ = max Cardinal.aleph0 (#σ) := by
      simpa using (Cardinal.add_eq_max (a := Cardinal.aleph0) (b := #σ) (by rfl))
    _ = max (#σ) Cardinal.aleph0 := by
      simp [max_comm]

theorem mk_FormulaH_le_BigKappa (σ : Type) :
    #(FormulaH σ (BigKappa σ)) ≤ #(BigKappa σ) := by
  classical
  -- Bound by `max #σ (max #κ ℵ₀)` and simplify using `#κ = max #σ ℵ₀`.
  have h :=
    mk_FormulaH_le_max (σ := σ) (κ := BigKappa σ)
  -- Rewrite `#(BigKappa σ)` and discharge the max simplifications.
  -- Note: `#(BigKappa σ) ≥ ℵ₀`, so `max (#(BigKappa σ)) ℵ₀ = #(BigKappa σ)`.
  have hk : #(BigKappa σ) = max (#σ) Cardinal.aleph0 := mk_BigKappa (σ := σ)
  -- Use `hk` to reduce the RHS of `h` to `#(BigKappa σ)`.
  -- `max #σ (max #κ ℵ₀) = #κ` when `#κ = max #σ ℵ₀`.
  simpa [hk, max_assoc, max_left_comm, max_comm, max_idem] using h

theorem exists_embed_requests_into_BigKappa (σ : Type) :
    Nonempty ((Var × FormulaH σ (BigKappa σ)) ↪ BigKappa σ) := by
  classical
  -- Show the cardinal inequality and use `Cardinal.le_def`.
  have hForm : #(FormulaH σ (BigKappa σ)) ≤ #(BigKappa σ) :=
    mk_FormulaH_le_BigKappa (σ := σ)
  have hVar : #Var ≤ #(BigKappa σ) := by
    -- `#Var = ℵ₀` and `BigKappa σ` is infinite.
    have hk : #(BigKappa σ) = max (#σ) Cardinal.aleph0 := mk_BigKappa (σ := σ)
    -- `ℵ₀ ≤ max #σ ℵ₀ = #κ`.
    have hAleph : Cardinal.aleph0 ≤ #(BigKappa σ) := by
      rw [hk]
      exact le_max_right (#σ) Cardinal.aleph0
    -- `Var = Nat`, so this is just `ℵ₀ ≤ #κ`.
    have hVarNat : #Var = Cardinal.aleph0 := by
      simp [Var]
    rw [hVarNat]
    exact hAleph
  have hkInf : Cardinal.aleph0 ≤ #(BigKappa σ) := by
    have hk : #(BigKappa σ) = max (#σ) Cardinal.aleph0 := mk_BigKappa (σ := σ)
    rw [hk]
    exact le_max_right (#σ) Cardinal.aleph0
  have hProd :
      #(Var × FormulaH σ (BigKappa σ)) ≤ #(BigKappa σ) := by
    -- `#(A×B) = #A * #B ≤ max (max #A #B) ℵ₀ ≤ #κ`.
    have hmul : (#Var) * #(FormulaH σ (BigKappa σ)) ≤
        max (max (#Var) (#(FormulaH σ (BigKappa σ)))) Cardinal.aleph0 :=
      Cardinal.mul_le_max (#Var) (#(FormulaH σ (BigKappa σ)))
    have hmax : max (max (#Var) (#(FormulaH σ (BigKappa σ)))) Cardinal.aleph0 ≤ #(BigKappa σ) := by
      refine max_le ?_ hkInf
      exact max_le hVar hForm
    -- Convert to the product type cardinal.
    simpa [Cardinal.mk_prod] using hmul.trans hmax
  -- Extract an embedding from the cardinal inequality.
  exact (Cardinal.le_def (Var × FormulaH σ (BigKappa σ)) (BigKappa σ)).1 hProd

/-! ### Stratified Witness Namespace (Research Track) -/

/--
`StratKappa σ := Nat × (σ ⊕ Nat)` is a stratified parameter namespace.

Intuition: the `Nat` level acts as a cheap “rank” so that we can choose witnesses at a strictly
higher level than all parameters already appearing in the requested formula.

This is intended as a concrete alternative to the abandoned `Ordinal.typein` plan:
it avoids universe escalation while still enabling acyclicity / well-founded “freshness by level”
arguments.
-/
abbrev StratKappa (σ : Type) : Type := Nat × BigKappa σ

theorem mk_StratKappa_eq_BigKappa (σ : Type) :
    #(StratKappa σ) = #(BigKappa σ) := by
  classical
  have hInf : Cardinal.aleph0 ≤ #(BigKappa σ) := by
    have hk : #(BigKappa σ) = max (#σ) Cardinal.aleph0 := mk_BigKappa (σ := σ)
    rw [hk]
    exact le_max_right (#σ) Cardinal.aleph0
  -- `#(Nat × α) = ℵ₀ * #α = #α` when `α` is infinite.
  calc
    #(StratKappa σ) = (#Nat) * #(BigKappa σ) := by
      simp [StratKappa, Cardinal.mk_prod]
    _ = Cardinal.aleph0 * #(BigKappa σ) := by
      simp
    _ = #(BigKappa σ) := by
      exact Cardinal.aleph0_mul_eq hInf

theorem mk_StratKappa (σ : Type) :
    #(StratKappa σ) = max (#σ) Cardinal.aleph0 := by
  -- Combine the previous lemma with the explicit computation for `BigKappa`.
  calc
    #(StratKappa σ) = #(BigKappa σ) := mk_StratKappa_eq_BigKappa (σ := σ)
    _ = max (#σ) Cardinal.aleph0 := mk_BigKappa (σ := σ)

theorem mk_FormulaH_le_StratKappa (σ : Type) :
    #(FormulaH σ (StratKappa σ)) ≤ #(StratKappa σ) := by
  classical
  have h := mk_FormulaH_le_max (σ := σ) (κ := StratKappa σ)
  have hk : #(StratKappa σ) = max (#σ) Cardinal.aleph0 := mk_StratKappa (σ := σ)
  simpa [hk, max_assoc, max_left_comm, max_comm, max_idem] using h

theorem exists_embed_requests_into_StratPayload (σ : Type) :
    Nonempty ((Var × FormulaH σ (StratKappa σ)) ↪ BigKappa σ) := by
  classical
  -- First embed requests into `StratKappa σ`, then use `#(StratKappa σ) = #(BigKappa σ)`.
  have hForm : #(FormulaH σ (StratKappa σ)) ≤ #(StratKappa σ) :=
    mk_FormulaH_le_StratKappa (σ := σ)
  have hVar : #Var ≤ #(StratKappa σ) := by
    -- `#Var = ℵ₀` and `StratKappa σ` is infinite since it contains `Nat`.
    have hk : #(StratKappa σ) = max (#σ) Cardinal.aleph0 := mk_StratKappa (σ := σ)
    have hAleph : Cardinal.aleph0 ≤ #(StratKappa σ) := by
      rw [hk]
      exact le_max_right (#σ) Cardinal.aleph0
    have hVarNat : #Var = Cardinal.aleph0 := by
      simp [Var]
    rw [hVarNat]
    exact hAleph
  have hkInf : Cardinal.aleph0 ≤ #(StratKappa σ) := by
    have hk : #(StratKappa σ) = max (#σ) Cardinal.aleph0 := mk_StratKappa (σ := σ)
    rw [hk]
    exact le_max_right (#σ) Cardinal.aleph0
  have hReqToStrat :
      #(Var × FormulaH σ (StratKappa σ)) ≤ #(StratKappa σ) := by
    have hmul : (#Var) * #(FormulaH σ (StratKappa σ)) ≤
        max (max (#Var) (#(FormulaH σ (StratKappa σ)))) Cardinal.aleph0 :=
      Cardinal.mul_le_max (#Var) (#(FormulaH σ (StratKappa σ)))
    have hmax : max (max (#Var) (#(FormulaH σ (StratKappa σ)))) Cardinal.aleph0 ≤ #(StratKappa σ) := by
      refine max_le ?_ hkInf
      exact max_le hVar hForm
    simpa [Cardinal.mk_prod] using hmul.trans hmax
  have hReqToPayload :
      #(Var × FormulaH σ (StratKappa σ)) ≤ #(BigKappa σ) := by
    -- Rewrite `#(StratKappa σ)` to `#(BigKappa σ)`.
    simpa [mk_StratKappa_eq_BigKappa (σ := σ)] using hReqToStrat
  exact (Cardinal.le_def (Var × FormulaH σ (StratKappa σ)) (BigKappa σ)).1 hReqToPayload

noncomputable def maxParamLevel (σ : Type) (φ : FormulaH σ (StratKappa σ)) : Nat := by
  classical
  exact (paramsFormula (σ := σ) (κ := StratKappa σ) φ).sup Prod.fst

theorem fst_le_maxParamLevel_of_mem
    (σ : Type) {φ : FormulaH σ (StratKappa σ)} {k : StratKappa σ}
    (hk : k ∈ paramsFormula (σ := σ) (κ := StratKappa σ) φ) :
    k.1 ≤ maxParamLevel (σ := σ) φ := by
  classical
  -- `sup` is `max` for `Nat`.
  simpa [maxParamLevel] using (Finset.le_sup hk : Prod.fst k ≤ _)

/--
Canonical “stratified” witness choice:
pick a payload code for the witness request, and place it at level `(maxParamLevel φ)+1`.

This ensures the chosen witness parameter does not already occur in `φ`.
-/
noncomputable def stratChoose (σ : Type) : Var → FormulaH σ (StratKappa σ) → StratKappa σ := by
  classical
  -- Choose an injective payload code for witness requests into `BigKappa σ`.
  let emb : (Var × FormulaH σ (StratKappa σ)) ↪ BigKappa σ :=
    Classical.choice (exists_embed_requests_into_StratPayload (σ := σ))
  exact fun x φ => (maxParamLevel (σ := σ) φ + 1, emb ⟨x, φ⟩)

theorem stratChoose_not_mem_paramsFormula
    (σ : Type) (x : Var) (φ : FormulaH σ (StratKappa σ)) :
    stratChoose (σ := σ) x φ ∉
      paramsFormula (σ := σ) (κ := StratKappa σ) φ := by
  classical
  intro hmem
  have hle :=
    fst_le_maxParamLevel_of_mem (σ := σ) (φ := φ) (k := stratChoose (σ := σ) x φ) hmem
  -- Contradiction: a level cannot be strictly larger than the maximum level.
  have hle' := hle
  simp [stratChoose] at hle'
  -- `simp` turns the inequality into `False`, closing the goal.

theorem stratChoose_injective (σ : Type) :
    Function.Injective (fun r : Var × FormulaH σ (StratKappa σ) => stratChoose (σ := σ) r.1 r.2) := by
  classical
  intro r₁ r₂ h
  -- Compare levels to deduce the requested formulas have the same max level.
  have hlevel :
      maxParamLevel (σ := σ) r₁.2 + 1 = maxParamLevel (σ := σ) r₂.2 + 1 := by
    exact congrArg Prod.fst h
  have _hmax : maxParamLevel (σ := σ) r₁.2 = maxParamLevel (σ := σ) r₂.2 := Nat.succ_inj.1 hlevel
  -- Compare payloads and use injectivity of the chosen embedding.
  -- Unfold once to expose the embedding.
  dsimp [stratChoose] at h
  -- `simp` can rewrite the pair equality; then `emb` injectivity finishes.
  have hpayload :
      (Classical.choice (exists_embed_requests_into_StratPayload (σ := σ))) r₁ =
        (Classical.choice (exists_embed_requests_into_StratPayload (σ := σ))) r₂ := by
    -- From equality of pairs, second components are equal.
    exact congrArg Prod.snd h
  have : r₁ = r₂ :=
    (Classical.choice (exists_embed_requests_into_StratPayload (σ := σ))).injective hpayload
  exact this

/-! ### Finite-support freshness supply for Henkin parameters -/

/--
Uniform interface: choose an element of `α` outside any given finite set.

This is the minimal freshness supply needed by one-step Henkin insertion arguments that only
depend on finite derivation support.
-/
class HasFreshFromFinset (α : Type) where
  fresh : Finset α → α
  fresh_not_mem : ∀ S : Finset α, fresh S ∉ S

theorem exists_fresh_not_mem_finset
    {α : Type} [HasFreshFromFinset α] (S : Finset α) :
    ∃ a : α, a ∉ S := by
  exact ⟨HasFreshFromFinset.fresh S, HasFreshFromFinset.fresh_not_mem S⟩

theorem exists_fresh_not_mem_paramsContext
    {σ κ : Type} [DecidableEq κ] [HasFreshFromFinset κ]
    (Γ : List (FormulaH σ κ)) :
    ∃ k : κ, k ∉ paramsContext (σ := σ) (κ := κ) Γ := by
  exact exists_fresh_not_mem_finset
    (S := paramsContext (σ := σ) (κ := κ) Γ)

theorem exists_fresh_not_mem_paramsContext_and_formula
    {σ κ : Type} [DecidableEq κ] [HasFreshFromFinset κ]
    (Γ : List (FormulaH σ κ)) (χ : FormulaH σ κ) :
    ∃ k : κ,
      k ∉ paramsContext (σ := σ) (κ := κ) Γ ∧
      k ∉ paramsFormula (σ := σ) (κ := κ) χ := by
  let S : Finset κ := paramsContext (σ := σ) (κ := κ) Γ ∪ paramsFormula (σ := σ) (κ := κ) χ
  refine ⟨HasFreshFromFinset.fresh S, ?_, ?_⟩
  ·
    intro hk
    exact HasFreshFromFinset.fresh_not_mem S (by
      exact Finset.mem_union.2 (Or.inl hk))
  ·
    intro hk
    exact HasFreshFromFinset.fresh_not_mem S (by
      exact Finset.mem_union.2 (Or.inr hk))

/-- Maximum right-`Nat` payload appearing in a finite `BigKappa` set (left payloads contribute `0`). -/
def maxNatInBigKappaFinset (σ : Type) (S : Finset (BigKappa σ)) : Nat :=
  S.sup (fun k =>
    match k with
    | Sum.inl _ => 0
    | Sum.inr n => n)

/-- Canonical fresh `BigKappa` point outside a finite set: one above its max right payload. -/
def freshBigKappaFromFinset (σ : Type) (S : Finset (BigKappa σ)) : BigKappa σ :=
  Sum.inr (maxNatInBigKappaFinset (σ := σ) S + 1)

theorem freshBigKappaFromFinset_not_mem (σ : Type) (S : Finset (BigKappa σ)) :
    freshBigKappaFromFinset (σ := σ) S ∉ S := by
  intro hmem
  have hle :
      maxNatInBigKappaFinset (σ := σ) S + 1 ≤ maxNatInBigKappaFinset (σ := σ) S := by
    have hle' :
        (fun k : BigKappa σ =>
          match k with
          | Sum.inl _ => 0
          | Sum.inr n => n) (freshBigKappaFromFinset (σ := σ) S) ≤
          S.sup (fun k : BigKappa σ =>
            match k with
            | Sum.inl _ => 0
            | Sum.inr n => n) :=
      Finset.le_sup
        (f := fun k : BigKappa σ =>
          match k with
          | Sum.inl _ => 0
          | Sum.inr n => n)
        hmem
    simpa [freshBigKappaFromFinset, maxNatInBigKappaFinset] using
      hle'
  exact (Nat.not_succ_le_self (maxNatInBigKappaFinset (σ := σ) S)) hle

instance hasFreshFromFinsetBigKappa (σ : Type) :
    HasFreshFromFinset (BigKappa σ) where
  fresh := freshBigKappaFromFinset (σ := σ)
  fresh_not_mem := freshBigKappaFromFinset_not_mem (σ := σ)

/-- Maximum stratification level appearing in a finite `StratKappa` set. -/
def maxLevelInStratKappaFinset (σ : Type) (S : Finset (StratKappa σ)) : Nat :=
  S.sup Prod.fst

/-- Canonical fresh `StratKappa` point outside a finite set: new level, fixed payload. -/
def freshStratKappaFromFinset (σ : Type) (S : Finset (StratKappa σ)) : StratKappa σ :=
  (maxLevelInStratKappaFinset (σ := σ) S + 1, Sum.inr 0)

theorem freshStratKappaFromFinset_not_mem (σ : Type) (S : Finset (StratKappa σ)) :
    freshStratKappaFromFinset (σ := σ) S ∉ S := by
  intro hmem
  have hle :
      maxLevelInStratKappaFinset (σ := σ) S + 1 ≤ maxLevelInStratKappaFinset (σ := σ) S := by
    have hle' :
        Prod.fst (freshStratKappaFromFinset (σ := σ) S) ≤
          S.sup Prod.fst :=
      Finset.le_sup hmem
    simpa [freshStratKappaFromFinset, maxLevelInStratKappaFinset] using
      hle'
  exact (Nat.not_succ_le_self (maxLevelInStratKappaFinset (σ := σ) S)) hle

instance hasFreshFromFinsetStratKappa (σ : Type) :
    HasFreshFromFinset (StratKappa σ) where
  fresh := freshStratKappaFromFinset (σ := σ)
  fresh_not_mem := freshStratKappaFromFinset_not_mem (σ := σ)

end HenkinCardinalBounds
end Noneism
end HeytingLean
