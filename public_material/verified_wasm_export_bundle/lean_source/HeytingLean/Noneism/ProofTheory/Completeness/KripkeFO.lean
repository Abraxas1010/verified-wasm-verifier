import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Zorn
import HeytingLean.Noneism.ProofTheory.Completeness.KripkeProp
import HeytingLean.Noneism.ProofTheory.Soundness.KripkeFO
import HeytingLean.Noneism.ProofTheory.Quantifiers.DerivedRules
import HeytingLean.Noneism.ProofTheory.Quantifiers.UniversalClosure

/-!
# Noneism.ProofTheory.Completeness.KripkeFO

First-order Kripke completeness interface for the `sigma/pi` ND system.

Trust boundary:
- `Soundness.KripkeFO` is fully internal and proved in Lean.
- Completeness for the full first-order intuitionistic fragment is tracked here as an explicit
  internal artifact interface (`HasInternalCountermodel` and canonical-obligation classes).
- This keeps downstream developments honest: all uses of completeness are machine-searchable and can
  later be replaced by an internal proof without API breakage.
-/

namespace HeytingLean
namespace Noneism
namespace KripkeFO
namespace Completeness

open Formula

variable {σ : Type}

/-! ## Fully internal completeness for the quantifier-free fragment -/

namespace PropFragment

/-- Identity valuation into the term domain. -/
def idValuation : Valuation Term := fun x => .var x

@[simp] theorem evalTerm_idValuation (t : Term) :
    evalTerm (idValuation) t = t := by
  cases t
  rfl

/--
Lift a propositional Kripke model to a first-order model over domain `Term`.

For quantifier-free formulas this makes `KripkeFO.Forces` definitionally coincide with
`KripkeProp.Forces` under `idValuation`.
-/
def liftPropModel {W : Type} [Preorder W] (M : KripkeProp.Model W σ) : Model W σ Term where
  valPred w p args := M.valPred w p args
  monoPred := by
    intro w v hwv p args h
    exact M.monoPred hwv p args h
  valEx w t := M.valEx w t
  monoEx := by
    intro w v hwv t h
    exact M.monoEx hwv t h

theorem forces_liftPropModel_id_iff
    {W : Type} [Preorder W] (M : KripkeProp.Model W σ) (w : W)
    {φ : Formula σ} (hφ : KripkeProp.IsProp (σ := σ) φ) :
    Forces (liftPropModel (σ := σ) M) (idValuation) w φ ↔ KripkeProp.Forces M w φ := by
  induction hφ generalizing w with
  | top =>
      simp [Forces, KripkeProp.Forces]
  | bot =>
      simp [Forces, KripkeProp.Forces]
  | pred p args =>
      have hMap : args.map (evalTerm idValuation) = args := by
        induction args with
        | nil =>
            rfl
        | cons t ts ih =>
            simp [evalTerm_idValuation, ih]
      simp [Forces, KripkeProp.Forces, liftPropModel, hMap]
  | eExists t =>
      simp [Forces, KripkeProp.Forces, liftPropModel]
  | not h ih =>
      simp [Forces, KripkeProp.Forces, ih]
  | and hφ hψ ihφ ihψ =>
      simp [Forces, KripkeProp.Forces, ihφ, ihψ]
  | or hφ hψ ihφ ihψ =>
      simp [Forces, KripkeProp.Forces, ihφ, ihψ]
  | imp hφ hψ ihφ ihψ =>
      simp [Forces, KripkeProp.Forces, ihφ, ihψ]

theorem entailsProp_of_entailsFO
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ)
    (hEnt : Entails (σ := σ) Γ φ) :
    KripkeProp.Entails (σ := σ) Γ φ := by
  intro W _ M w hw
  let MF : Model W σ Term := liftPropModel (σ := σ) M
  have hwFO : ∀ ψ ∈ Γ, Forces MF idValuation w ψ := by
    intro ψ hψ
    exact (forces_liftPropModel_id_iff (σ := σ) (M := M) (w := w) (hφ := hΓ ψ hψ)).2 (hw ψ hψ)
  have hφFO : Forces MF idValuation w φ :=
    hEnt (W := W) (D := Term) (M := MF) (ρ := idValuation) (w := w) hwFO
  exact (forces_liftPropModel_id_iff (σ := σ) (M := M) (w := w) (hφ := hφ)).1 hφFO

end PropFragment

theorem completeness_prop_fragment
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    Entails (σ := σ) Γ φ → Derives (σ := σ) Γ φ := by
  intro hEnt
  have hEntProp : KripkeProp.Entails (σ := σ) Γ φ :=
    PropFragment.entailsProp_of_entailsFO (σ := σ) hΓ hφ hEnt
  have hDerProp : DerivesProp (σ := σ) Γ φ :=
    KripkeProp.Completeness.completeness (σ := σ) hΓ hφ hEntProp
  exact Derives.ofDerivesProp hDerProp

/-! ## Internal FO canonical/Henkin scaffolding -/

namespace InternalFO

/--
`Derivable T φ` means: there is a finite ND context from `T` deriving `φ`.

This is the first-order counterpart of the propositional helper used in
`Completeness.KripkeProp`, but now based on full `Derives`.
-/
def Derivable (T : Set (Formula σ)) (φ : Formula σ) : Prop :=
  ∃ Γ : List (Formula σ), (∀ ψ ∈ Γ, ψ ∈ T) ∧ Derives (σ := σ) Γ φ

/-- Consistency of a theory in terms of finitary ND derivability. -/
def Consistent (T : Set (Formula σ)) : Prop :=
  ¬ Derivable (σ := σ) T (.bot : Formula σ)

lemma derivable_of_mem {T : Set (Formula σ)} {φ : Formula σ} (hφ : φ ∈ T) :
    Derivable (σ := σ) T φ := by
  refine ⟨[φ], ?_, ?_⟩
  · intro ψ hψ
    simp at hψ
    subst hψ
    exact hφ
  · exact Derives.hyp (by simp)

lemma derivable_of_derives {T : Set (Formula σ)} {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, ψ ∈ T) (h : Derives (σ := σ) Γ φ) :
    Derivable (σ := σ) T φ :=
  ⟨Γ, hΓ, h⟩

lemma Derivable.mono {T U : Set (Formula σ)} {φ : Formula σ} (hTU : T ⊆ U) :
    Derivable (σ := σ) T φ → Derivable (σ := σ) U φ := by
  rintro ⟨Γ, hΓ, hDer⟩
  exact ⟨Γ, by intro ψ hψ; exact hTU (hΓ ψ hψ), hDer⟩

/-! ### Lindenbaum family infrastructure for first-order `Derives` -/

namespace Lindenbaum

open scoped Classical

/-- Zorn family: consistent extensions of `S` that do not derive `χ`. -/
def Family (S : Set (Formula σ)) (χ : Formula σ) : Set (Set (Formula σ)) :=
  {T | Consistent (σ := σ) T ∧ S ⊆ T ∧ ¬ Derivable (σ := σ) T χ}

/-- Closedness predicate for sentence theories. -/
def SentenceClosed (T : Set (Formula σ)) : Prop :=
  ∀ ψ, ψ ∈ T → Syntax.fvFormula (σ := σ) ψ = ∅

/--
Sentence-restricted Lindenbaum family:
consistent extensions of `S` that avoid deriving `χ` and contain only closed formulas.
-/
def SentenceFamily (S : Set (Formula σ)) (χ : Formula σ) : Set (Set (Formula σ)) :=
  {T | T ∈ Family (σ := σ) S χ ∧ SentenceClosed (σ := σ) T}

lemma sentenceFamily_subset_family {S : Set (Formula σ)} {χ : Formula σ} :
    SentenceFamily (σ := σ) S χ ⊆ Family (σ := σ) S χ := by
  intro T hT
  exact hT.1

lemma family_mem_of_base {S : Set (Formula σ)} {χ : Formula σ}
    (hS : Consistent (σ := σ) S) (hχ : ¬ Derivable (σ := σ) S χ) :
    S ∈ Family (σ := σ) S χ := by
  refine ⟨hS, ?_, hχ⟩
  intro φ hφ
  exact hφ

lemma chain_directedOn {α : Type} {c : Set (Set α)}
    (hc : IsChain (· ⊆ ·) c) : DirectedOn (· ⊆ ·) c := by
  intro a ha b hb
  rcases hc.total ha hb with hab | hba
  · exact ⟨b, hb, hab, subset_rfl⟩
  · exact ⟨a, ha, subset_rfl, hba⟩

lemma sUnion_mem_family {S : Set (Formula σ)} {χ : Formula σ}
    {c : Set (Set (Formula σ))}
    (hcF : c ⊆ Family (σ := σ) S χ)
    (hc : IsChain (· ⊆ ·) c)
    (hcne : c.Nonempty) :
    Set.sUnion c ∈ Family (σ := σ) S χ := by
  classical
  refine ⟨?consistent, ?base, ?notDerivable⟩
  · intro hbot
    rcases hbot with ⟨Γ, hΓ, hDerBot⟩
    let fs : Finset (Formula σ) := Γ.toFinset
    have hfsfin : (fs : Set (Formula σ)).Finite := fs.finite_toSet
    have hfsSub : (fs : Set (Formula σ)) ⊆ Set.sUnion c := by
      intro φ hφ
      have : φ ∈ Γ := List.mem_toFinset.1 hφ
      exact hΓ φ this
    have hdir : DirectedOn (· ⊆ ·) c := chain_directedOn (hc := hc)
    rcases
        DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion
          (α := Formula σ) (c := c) hcne hdir (s := (fs : Set (Formula σ))) hfsfin hfsSub with
      ⟨t, htC, hfst⟩
    have hΓt : ∀ ψ ∈ Γ, ψ ∈ t := by
      intro ψ hψ
      have : ψ ∈ (fs : Set (Formula σ)) := List.mem_toFinset.2 hψ
      exact hfst this
    have htCons : Consistent (σ := σ) t := (hcF htC).1
    exact htCons (derivable_of_derives (σ := σ) (T := t) (Γ := Γ) (φ := .bot)
      (by intro ψ hψ; exact hΓt ψ hψ) hDerBot)
  · intro φ hφ
    rcases hcne with ⟨t, htC⟩
    have hSt : S ⊆ t := (hcF htC).2.1
    exact Set.subset_sUnion_of_mem htC (hSt hφ)
  · intro hχ
    rcases hχ with ⟨Γ, hΓ, hDerχ⟩
    let fs : Finset (Formula σ) := Γ.toFinset
    have hfsfin : (fs : Set (Formula σ)).Finite := fs.finite_toSet
    have hfsSub : (fs : Set (Formula σ)) ⊆ Set.sUnion c := by
      intro φ hφ
      have : φ ∈ Γ := List.mem_toFinset.1 hφ
      exact hΓ φ this
    have hdir : DirectedOn (· ⊆ ·) c := chain_directedOn (hc := hc)
    rcases
        DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion
          (α := Formula σ) (c := c) hcne hdir (s := (fs : Set (Formula σ))) hfsfin hfsSub with
      ⟨t, htC, hfst⟩
    have hΓt : ∀ ψ ∈ Γ, ψ ∈ t := by
      intro ψ hψ
      have : ψ ∈ (fs : Set (Formula σ)) := List.mem_toFinset.2 hψ
      exact hfst this
    have htNo : ¬ Derivable (σ := σ) t χ := (hcF htC).2.2
    exact htNo (derivable_of_derives (σ := σ) (T := t) (Γ := Γ) (φ := χ)
      (by intro ψ hψ; exact hΓt ψ hψ) hDerχ)

/-- Existence of a maximal element of `Family S χ` extending `S`. -/
theorem exists_maximal (S : Set (Formula σ)) (χ : Formula σ)
    (hS : Consistent (σ := σ) S) (hχ : ¬ Derivable (σ := σ) S χ) :
    ∃ M : Set (Formula σ), S ⊆ M ∧ Maximal (· ∈ Family (σ := σ) S χ) M := by
  classical
  have hmem : S ∈ Family (σ := σ) S χ := family_mem_of_base (σ := σ) (S := S) (χ := χ) hS hχ
  have H :
      ∀ c ⊆ Family (σ := σ) S χ,
        IsChain (· ⊆ ·) c →
          c.Nonempty →
            ∃ ub ∈ Family (σ := σ) S χ, ∀ s ∈ c, s ⊆ ub := by
    intro c hcF hc hcne
    refine ⟨Set.sUnion c, ?_, ?_⟩
    · exact sUnion_mem_family (σ := σ) (S := S) (χ := χ) (c := c) hcF hc hcne
    · intro s hs
      exact Set.subset_sUnion_of_mem hs
  rcases zorn_subset_nonempty (Family (σ := σ) S χ) H S hmem with ⟨M, hSM, hMax⟩
  exact ⟨M, hSM, hMax⟩

lemma sentenceFamily_mem_of_base {S : Set (Formula σ)} {χ : Formula σ}
    (hS : Consistent (σ := σ) S)
    (hχ : ¬ Derivable (σ := σ) S χ)
    (hSClosed : SentenceClosed (σ := σ) S) :
    S ∈ SentenceFamily (σ := σ) S χ := by
  exact ⟨family_mem_of_base (σ := σ) (S := S) (χ := χ) hS hχ, hSClosed⟩

lemma sUnion_sentenceClosed {S : Set (Formula σ)} {χ : Formula σ}
    {c : Set (Set (Formula σ))}
    (hcF : c ⊆ SentenceFamily (σ := σ) S χ) :
    SentenceClosed (σ := σ) (Set.sUnion c) := by
  intro ψ hψ
  rcases Set.mem_sUnion.1 hψ with ⟨t, htC, hψt⟩
  exact (hcF htC).2 ψ hψt

lemma sUnion_mem_sentenceFamily {S : Set (Formula σ)} {χ : Formula σ}
    {c : Set (Set (Formula σ))}
    (hcF : c ⊆ SentenceFamily (σ := σ) S χ)
    (hc : IsChain (· ⊆ ·) c)
    (hcne : c.Nonempty) :
    Set.sUnion c ∈ SentenceFamily (σ := σ) S χ := by
  refine ⟨?_, sUnion_sentenceClosed (σ := σ) (S := S) (χ := χ) (c := c) hcF⟩
  exact sUnion_mem_family (σ := σ) (S := S) (χ := χ)
    (c := c)
    (hcF := by
      intro t ht
      exact (hcF ht).1)
    (hc := hc)
    (hcne := hcne)

/--
Existence of a maximal sentence-closed element of `SentenceFamily S χ` extending `S`.
-/
theorem exists_maximal_sentence (S : Set (Formula σ)) (χ : Formula σ)
    (hS : Consistent (σ := σ) S)
    (hχ : ¬ Derivable (σ := σ) S χ)
    (hSClosed : SentenceClosed (σ := σ) S) :
    ∃ M : Set (Formula σ), S ⊆ M ∧ Maximal (· ∈ SentenceFamily (σ := σ) S χ) M := by
  classical
  have hmem : S ∈ SentenceFamily (σ := σ) S χ :=
    sentenceFamily_mem_of_base (σ := σ) (S := S) (χ := χ) hS hχ hSClosed
  have H :
      ∀ c ⊆ SentenceFamily (σ := σ) S χ,
        IsChain (· ⊆ ·) c →
          c.Nonempty →
            ∃ ub ∈ SentenceFamily (σ := σ) S χ, ∀ s ∈ c, s ⊆ ub := by
    intro c hcF hc hcne
    refine ⟨Set.sUnion c, ?_, ?_⟩
    · exact sUnion_mem_sentenceFamily (σ := σ) (S := S) (χ := χ)
        (c := c) hcF hc hcne
    · intro s hs
      exact Set.subset_sUnion_of_mem hs
  rcases zorn_subset_nonempty (SentenceFamily (σ := σ) S χ) H S hmem with
    ⟨M, hSM, hMax⟩
  exact ⟨M, hSM, hMax⟩

lemma maximal_sentence_mem_family {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)}
    (hMax : Maximal (· ∈ SentenceFamily (σ := σ) S χ) M) :
    M ∈ Family (σ := σ) S χ :=
  (hMax.prop).1

lemma maximal_sentence_closed {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)}
    (hMax : Maximal (· ∈ SentenceFamily (σ := σ) S χ) M) :
    SentenceClosed (σ := σ) M :=
  (hMax.prop).2

lemma goal_not_mem_of_sentenceFamily {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)}
    (hMF : M ∈ SentenceFamily (σ := σ) S χ) :
    χ ∉ M := by
  intro hχMem
  exact hMF.1.2.2 (derivable_of_mem (σ := σ) (T := M) hχMem)

/--
List-context entry point to sentence-family maximality.

From a non-derivable sequent with closed premises, obtain a maximal sentence-family extension
over the associated set-theory base.
-/
theorem exists_maximal_sentence_of_notDerives
    (hWeak :
      ∀ {Γ Δ : List (Formula σ)} {φ : Formula σ},
        Derives (σ := σ) Γ φ →
        Γ ⊆ Δ →
        Derives (σ := σ) Δ φ)
    {Γ : List (Formula σ)} {χ : Formula σ}
    (hΓClosed : ∀ ψ, ψ ∈ Γ → Syntax.fvFormula (σ := σ) ψ = ∅)
    (hNotDer : ¬ Derives (σ := σ) Γ χ) :
    ∃ M : Set (Formula σ),
      ({ψ | ψ ∈ Γ} ⊆ M) ∧
      Maximal (· ∈ SentenceFamily (σ := σ) {ψ | ψ ∈ Γ} χ) M := by
  let S : Set (Formula σ) := {ψ | ψ ∈ Γ}
  have hSCons : Consistent (σ := σ) S := by
    intro hDerBot
    rcases hDerBot with ⟨Δ, hΔS, hDerΔBot⟩
    have hSub : Δ ⊆ Γ := by
      intro ψ hψ
      exact hΔS ψ hψ
    have hDerΓBot : Derives (σ := σ) Γ (.bot : Formula σ) :=
      hWeak hDerΔBot hSub
    exact hNotDer (Derives.botE hDerΓBot)
  have hNoχ : ¬ Derivable (σ := σ) S χ := by
    intro hDerχ
    rcases hDerχ with ⟨Δ, hΔS, hDerΔχ⟩
    have hSub : Δ ⊆ Γ := by
      intro ψ hψ
      exact hΔS ψ hψ
    exact hNotDer (hWeak hDerΔχ hSub)
  have hSClosed : SentenceClosed (σ := σ) S := by
    intro ψ hψ
    exact hΓClosed ψ hψ
  exact exists_maximal_sentence (σ := σ) (S := S) (χ := χ) hSCons hNoχ hSClosed

/--
Semantic "cut" for derivability from sets:

If `θ` is derivable from `T` and `χ` is derivable from `insert θ T`, then `χ` is derivable from `T`.

The proof avoids unrestricted ND weakening by routing through semantic entailment and a provided
completeness oracle `hComplete` (for list contexts).
-/
lemma derivable_of_insert_of_derivable
    {T : Set (Formula σ)} {θ χ : Formula σ}
    (hWeak :
      ∀ {Γ Δ : List (Formula σ)} {φ : Formula σ},
        Derives (σ := σ) Γ φ →
        Γ ⊆ Δ →
        Derives (σ := σ) Δ φ)
    (hθ : Derivable (σ := σ) T θ)
    (hχIns : Derivable (σ := σ) (Set.insert θ T) χ) :
    Derivable (σ := σ) T χ := by
  rcases hθ with ⟨Γθ, hΓθT, hDerθ⟩
  rcases hχIns with ⟨Δ, hΔIns, hDerΔχ⟩
  classical
  let ΔT : List (Formula σ) := Δ.filter (fun t => decide (t ≠ θ))
  have hΔTT : ∀ t ∈ ΔT, t ∈ T := by
    intro t ht
    have htΔ : t ∈ Δ := (List.mem_filter.1 ht).1
    have htIns : t ∈ Set.insert θ T := hΔIns t htΔ
    rcases htIns with htEq | htT
    · have htne : t ≠ θ := (decide_eq_true_iff).1 (List.mem_filter.1 ht).2
      exact False.elim (htne htEq)
    · exact htT
  have hSubΔ : Δ ⊆ (θ :: ΔT) := by
    intro t ht
    by_cases hEq : t = θ
    · subst hEq
      simp
    · have htΔT : t ∈ ΔT := by
        refine List.mem_filter.2 ?_
        exact ⟨ht, (decide_eq_true_iff).2 hEq⟩
      simp [htΔT]
  have hDerCons : Derives (σ := σ) (θ :: ΔT) χ :=
    hWeak hDerΔχ hSubΔ
  have hDerImp : Derives (σ := σ) ΔT (.imp θ χ) :=
    Derives.impI hDerCons
  have hDerImpLift : Derives (σ := σ) (ΔT ++ Γθ) (.imp θ χ) :=
    hWeak hDerImp (by
      intro ψ hψ
      exact List.mem_append_left _ hψ)
  have hDerθLift : Derives (σ := σ) (ΔT ++ Γθ) θ :=
    hWeak hDerθ (by
      intro ψ hψ
      exact List.mem_append_right _ hψ)
  exact ⟨ΔT ++ Γθ, by
    intro t ht
    rcases List.mem_append.1 ht with htΔT | htΓθ
    · exact hΔTT t htΔT
    · exact hΓθT t htΓθ
    , Derives.impE hDerImpLift hDerθLift⟩

/--
Normalize a derivation from `insert θ T` into a one-premise sequent shape:
`Derives (θ :: Γ) χ` with all remaining assumptions in `T`.

This is the eigenvariable-safe format needed for sigma-elimination style arguments.
-/
lemma derives_cons_of_derivable_insert
    {T : Set (Formula σ)} {θ χ : Formula σ}
    (hWeak :
      ∀ {Γ Δ : List (Formula σ)} {φ : Formula σ},
        Derives (σ := σ) Γ φ →
        Γ ⊆ Δ →
        Derives (σ := σ) Δ φ)
    (hχIns : Derivable (σ := σ) (Set.insert θ T) χ) :
    ∃ Γ : List (Formula σ), (∀ ψ ∈ Γ, ψ ∈ T) ∧ Derives (σ := σ) (θ :: Γ) χ := by
  rcases hχIns with ⟨Δ, hΔIns, hDerΔχ⟩
  classical
  let Γ : List (Formula σ) := Δ.filter (fun t => decide (t ≠ θ))
  have hΓT : ∀ t ∈ Γ, t ∈ T := by
    intro t ht
    have htΔ : t ∈ Δ := (List.mem_filter.1 ht).1
    have htIns : t ∈ Set.insert θ T := hΔIns t htΔ
    rcases htIns with htEq | htT
    · have htne : t ≠ θ := (decide_eq_true_iff).1 (List.mem_filter.1 ht).2
      exact False.elim (htne htEq)
    · exact htT
  have hSub : Δ ⊆ (θ :: Γ) := by
    intro ξ hξ
    by_cases hEq : ξ = θ
    · subst hEq
      simp
    · have hξΓ : ξ ∈ Γ := by
        refine List.mem_filter.2 ?_
        exact ⟨hξ, (decide_eq_true_iff).2 hEq⟩
      simp [hξΓ]
  exact ⟨Γ, hΓT, hWeak hDerΔχ hSub⟩

/--
If inserting `θ` into a maximal-family candidate is not in the family, then `χ` is derivable
from that insertion.

This packages the "either inconsistent or derives χ" branch into a single derivability witness.
-/
lemma derivable_chi_of_not_family
    {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)} {θ : Formula σ}
    (hMF : M ∈ Family (σ := σ) S χ)
    (hNotFamIns : Set.insert θ M ∉ Family (σ := σ) S χ) :
    Derivable (σ := σ) (Set.insert θ M) χ := by
  classical
  by_contra hNoχ
  have hConsIns : Consistent (σ := σ) (Set.insert θ M) := by
    intro hBotIns
    rcases hBotIns with ⟨Γ, hΓ, hDerBot⟩
    exact hNoχ ⟨Γ, hΓ, Derives.botE hDerBot⟩
  have hFamIns : Set.insert θ M ∈ Family (σ := σ) S χ := by
    refine ⟨hConsIns, ?_, hNoχ⟩
    intro t ht
    exact Or.inr ((hMF.2.1) ht)
  exact hNotFamIns hFamIns

/--
From derivability of `χ` after inserting `θ`, derive implication `θ → χ` from the base theory.
-/
lemma derivable_imp_of_derivable_insert
    {T : Set (Formula σ)} {θ χ : Formula σ}
    (hWeak :
      ∀ {Γ Δ : List (Formula σ)} {φ : Formula σ},
        Derives (σ := σ) Γ φ →
        Γ ⊆ Δ →
        Derives (σ := σ) Δ φ)
    (hχIns : Derivable (σ := σ) (Set.insert θ T) χ) :
    Derivable (σ := σ) T (.imp θ χ) := by
  rcases derives_cons_of_derivable_insert (σ := σ) (T := T) (θ := θ) (χ := χ) hWeak hχIns with
    ⟨Γ, hΓT, hDerCons⟩
  exact ⟨Γ, hΓT, Derives.impI hDerCons⟩

/--
Semantic witness-change for quantifier instances in a fixed context:
if `χ` is derivable from `x ↦ a` plus `Γ`, then it is also derivable from `x ↦ b` plus `Γ`,
provided `a` is fresh for `Γ, χ` and both witnesses avoid `varsFormula φ`.
-/
lemma derives_witness_change_via_complete
    {Γ : List (Formula σ)} {x a b : Var} {φ χ : Formula σ}
    (hComplete :
      ∀ {Γ : List (Formula σ)} {ψ : Formula σ},
        Entails (σ := σ) Γ ψ → Derives (σ := σ) Γ ψ)
    (haΓ : a ∉ ND.fvContext (σ := σ) Γ)
    (haVars : a ∉ Syntax.varsFormula (σ := σ) φ)
    (hbVars : b ∉ Syntax.varsFormula (σ := σ) φ)
    (haχ : a ∉ Syntax.fvFormula (σ := σ) χ)
    (hDer : Derives (σ := σ) (Syntax.substFormula (σ := σ) x (.var a) φ :: Γ) χ) :
    Derives (σ := σ) (Syntax.substFormula (σ := σ) x (.var b) φ :: Γ) χ := by
  have hEntA :
      Entails (σ := σ) (Syntax.substFormula (σ := σ) x (.var a) φ :: Γ) χ :=
    KripkeFO.soundness (σ := σ) hDer
  have hEntB :
      Entails (σ := σ) (Syntax.substFormula (σ := σ) x (.var b) φ :: Γ) χ := by
    intro W _ D M ρ w hCtx
    let ρa : Valuation D := update ρ a (ρ b)
    have hΓρa : ∀ θ ∈ Γ, Forces M ρa w θ := by
      intro θ hθ
      have hnot : a ∉ Syntax.fvFormula (σ := σ) θ :=
        HeytingLean.Noneism.KripkeFO.NDHelpers.not_mem_fvFormula_of_not_mem_fvContext
          (σ := σ) (Γ := Γ) (a := a) haΓ hθ
      exact (KripkeFO.forces_update_of_not_mem_fvFormula
        (σ := σ) (M := M) (ρ := ρ) (y := a) (d := ρ b) θ hnot w).2
        (hCtx θ (by simp [hθ]))
    have hAssmB :
        Forces M ρ w (Syntax.substFormula (σ := σ) x (.var b) φ) :=
      hCtx _ (by simp)
    have hBodyB :
        Forces M (update ρ x (ρ b)) w φ :=
      (KripkeFO.forces_substFormula_var_of_not_mem_varsFormula
        (σ := σ) (M := M) (ρ := ρ) (w := w) x b φ hbVars).1 hAssmB
    have hBodyA :
        Forces M (update ρa x (ρa a)) w φ := by
      by_cases hax : a = x
      · subst hax
        simpa [ρa, update_update_same, update_self] using hBodyB
      ·
        have htmp : Forces M (update (update ρ x (ρ b)) a (ρ b)) w φ :=
          (KripkeFO.forces_update_of_not_mem_varsFormula
            (σ := σ) (M := M)
            (ρ := update ρ x (ρ b)) (y := a) (d := ρ b) (w := w) φ haVars).2 hBodyB
        have hcomm :
            update (update ρ x (ρ b)) a (ρ b) = update (update ρ a (ρ b)) x (ρ b) := by
          simpa using
            (update_comm (ρ := ρ) (x := x) (y := a) (dx := ρ b) (dy := ρ b) (Ne.symm hax))
        have : Forces M (update (update ρ a (ρ b)) x (ρ b)) w φ := by
          simpa [hcomm] using htmp
        simpa [ρa, update_self] using this
    have hAssmA :
        Forces M ρa w (Syntax.substFormula (σ := σ) x (.var a) φ) :=
      (KripkeFO.forces_substFormula_var_of_not_mem_varsFormula
        (σ := σ) (M := M) (ρ := ρa) (w := w) x a φ haVars).2 hBodyA
    have hCtxA :
        ∀ θ ∈ (Syntax.substFormula (σ := σ) x (.var a) φ :: Γ), Forces M ρa w θ := by
      intro θ hθ
      rcases List.mem_cons.1 hθ with rfl | hθΓ
      · exact hAssmA
      · exact hΓρa θ hθΓ
    have hχρa : Forces M ρa w χ := hEntA W D M ρa w hCtxA
    exact (KripkeFO.forces_update_of_not_mem_fvFormula
      (σ := σ) (M := M) (ρ := ρ) (y := a) (d := ρ b) χ haχ w).1 hχρa
  exact hComplete hEntB

/--
Purely syntactic witness-change for quantifier instances in a fixed context.

This version does not rely on semantic completeness. It transports a derivation
from `x ↦ a` to `x ↦ b` by deriving `sigma x φ` from the `b`-instance assumption
and eliminating it with witness `a`.
-/
lemma derives_witness_change
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

This packages the standard "pick a fresh witness and transport" pattern into one reusable lemma.
-/
lemma derives_witness_change_to_freshSigmaEigen
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
  let b : Var := ND.freshSigmaEigen (σ := σ) Γ φ χ
  have hbΓ : b ∉ ND.fvContext (σ := σ) Γ :=
    ND.freshSigmaEigen_not_mem_fvContext (σ := σ) Γ φ χ
  have hbVars : b ∉ Syntax.varsFormula (σ := σ) φ :=
    ND.freshSigmaEigen_not_mem_varsFormula (σ := σ) Γ φ χ
  have hbχ : b ∉ Syntax.fvFormula (σ := σ) χ :=
    ND.freshSigmaEigen_not_mem_fvFormula (σ := σ) Γ φ χ
  by_cases hEq : b = a
  · subst hEq
    exact ⟨b, hbΓ, hbVars, hbχ, hDer⟩
  ·
    have hDer' :
        Derives (σ := σ) (Syntax.substFormula (σ := σ) x (.var b) φ :: Γ) χ :=
      ND.derives_witness_change
        (σ := σ) (Γ := Γ) (x := x) (a := a) (b := b) (φ := φ) (χ := χ)
        haΓ haVars hbVars (Ne.symm hEq) haχ hDer
    exact ⟨b, hbΓ, hbVars, hbχ, hDer'⟩

/--
Source-fresh extraction variant for inserted witness derivations.

If the extracted one-premise shape already has source freshness, we can automatically transport it
to a fresh witness suitable for sigma-elimination.
-/
lemma fresh_cons_of_derivable_insert_of_source_fresh
    {T : Set (Formula σ)} {x a : Var} {φ χ : Formula σ}
    (hWeak :
      ∀ {Γ Δ : List (Formula σ)} {ψ : Formula σ},
        Derives (σ := σ) Γ ψ →
        Γ ⊆ Δ →
        Derives (σ := σ) Δ ψ)
    (haVars : a ∉ Syntax.varsFormula (σ := σ) φ)
    (haχ : a ∉ Syntax.fvFormula (σ := σ) χ)
    (hχIns : Derivable (σ := σ) (Set.insert (Syntax.substFormula (σ := σ) x (.var a) φ) T) χ)
    (hSourceFresh :
      ∀ Γ : List (Formula σ),
        (∀ ψ ∈ Γ, ψ ∈ T) →
        Derives (σ := σ) (Syntax.substFormula (σ := σ) x (.var a) φ :: Γ) χ →
        a ∉ ND.fvContext (σ := σ) Γ) :
    ∃ b : Var, ∃ Γ : List (Formula σ),
      b ∉ ND.fvContext (σ := σ) Γ ∧
      b ∉ Syntax.varsFormula (σ := σ) φ ∧
      b ∉ Syntax.fvFormula (σ := σ) χ ∧
      (∀ ψ ∈ Γ, ψ ∈ T) ∧
      Derives (σ := σ) (Syntax.substFormula (σ := σ) x (.var b) φ :: Γ) χ := by
  rcases derives_cons_of_derivable_insert
    (σ := σ) (T := T) (θ := Syntax.substFormula (σ := σ) x (.var a) φ) (χ := χ) hWeak hχIns with
    ⟨Γ, hΓT, hDerCons⟩
  have haΓ : a ∉ ND.fvContext (σ := σ) Γ := hSourceFresh Γ hΓT hDerCons
  rcases derives_witness_change_to_freshSigmaEigen
    (σ := σ) (Γ := Γ) (x := x) (a := a) (φ := φ) (χ := χ)
    haΓ haVars haχ hDerCons with
    ⟨b, hbΓ, hbVars, hbχ, hDerB⟩
  exact ⟨b, Γ, hbΓ, hbVars, hbχ, hΓT, hDerB⟩

/--
If all formulas in a background theory are fresh in `a`, any finite context extracted from that
theory is also fresh in `a`.
-/
lemma source_fresh_context_of_subset_theory_fresh
    {T : Set (Formula σ)} {a : Var}
    (hTheoryFresh : ∀ ψ, ψ ∈ T → a ∉ Syntax.fvFormula (σ := σ) ψ) :
    ∀ Γ : List (Formula σ), (∀ ψ ∈ Γ, ψ ∈ T) → a ∉ ND.fvContext (σ := σ) Γ := by
  intro Γ hΓT haCtx
  rcases (ND.mem_fvContext_iff (σ := σ) (x := a) (Γ := Γ)).1 haCtx with ⟨ψ, hψΓ, haψ⟩
  exact (hTheoryFresh ψ (hΓT ψ hψΓ)) haψ

/--
Fresh-cons extraction from inserted derivations when the base theory is already fresh in `a`.

This discharges the source-fresh side condition automatically from a theory-level freshness fact.
-/
lemma fresh_cons_of_derivable_insert_of_theory_fresh
    {T : Set (Formula σ)} {x a : Var} {φ χ : Formula σ}
    (hWeak :
      ∀ {Γ Δ : List (Formula σ)} {ψ : Formula σ},
        Derives (σ := σ) Γ ψ →
        Γ ⊆ Δ →
        Derives (σ := σ) Δ ψ)
    (haVars : a ∉ Syntax.varsFormula (σ := σ) φ)
    (haχ : a ∉ Syntax.fvFormula (σ := σ) χ)
    (hTheoryFresh : ∀ ψ, ψ ∈ T → a ∉ Syntax.fvFormula (σ := σ) ψ)
    (hχIns : Derivable (σ := σ) (Set.insert (Syntax.substFormula (σ := σ) x (.var a) φ) T) χ) :
    ∃ b : Var, ∃ Γ : List (Formula σ),
      b ∉ ND.fvContext (σ := σ) Γ ∧
      b ∉ Syntax.varsFormula (σ := σ) φ ∧
      b ∉ Syntax.fvFormula (σ := σ) χ ∧
      (∀ ψ ∈ Γ, ψ ∈ T) ∧
      Derives (σ := σ) (Syntax.substFormula (σ := σ) x (.var b) φ :: Γ) χ := by
  have hSourceFresh :
      ∀ Γ : List (Formula σ),
        (∀ ψ ∈ Γ, ψ ∈ T) →
        Derives (σ := σ) (Syntax.substFormula (σ := σ) x (.var a) φ :: Γ) χ →
        a ∉ ND.fvContext (σ := σ) Γ := by
    intro Γ hΓT _hDer
    exact source_fresh_context_of_subset_theory_fresh
      (σ := σ) (T := T) (a := a) hTheoryFresh Γ hΓT
  exact Lindenbaum.fresh_cons_of_derivable_insert_of_source_fresh
    (σ := σ) (T := T) (x := x) (a := a) (φ := φ) (χ := χ)
    hWeak haVars haχ hχIns hSourceFresh

/--
Fresh-cons extraction from inserted derivations for closed background theories.

This is a direct corollary of the theory-fresh bridge, since closed formulas have empty free vars.
-/
lemma fresh_cons_of_derivable_insert_of_theory_closed
    {T : Set (Formula σ)} {x a : Var} {φ χ : Formula σ}
    (hWeak :
      ∀ {Γ Δ : List (Formula σ)} {ψ : Formula σ},
        Derives (σ := σ) Γ ψ →
        Γ ⊆ Δ →
        Derives (σ := σ) Δ ψ)
    (haVars : a ∉ Syntax.varsFormula (σ := σ) φ)
    (haχ : a ∉ Syntax.fvFormula (σ := σ) χ)
    (hTheoryClosed : ∀ ψ, ψ ∈ T → Syntax.fvFormula (σ := σ) ψ = ∅)
    (hχIns : Derivable (σ := σ) (Set.insert (Syntax.substFormula (σ := σ) x (.var a) φ) T) χ) :
    ∃ b : Var, ∃ Γ : List (Formula σ),
      b ∉ ND.fvContext (σ := σ) Γ ∧
      b ∉ Syntax.varsFormula (σ := σ) φ ∧
      b ∉ Syntax.fvFormula (σ := σ) χ ∧
      (∀ ψ ∈ Γ, ψ ∈ T) ∧
      Derives (σ := σ) (Syntax.substFormula (σ := σ) x (.var b) φ :: Γ) χ := by
  have hTheoryFresh : ∀ ψ, ψ ∈ T → a ∉ Syntax.fvFormula (σ := σ) ψ := by
    intro ψ hψ ha
    simp [hTheoryClosed ψ hψ] at ha
  exact Lindenbaum.fresh_cons_of_derivable_insert_of_theory_fresh
    (σ := σ) (T := T) (x := x) (a := a) (φ := φ) (χ := χ)
    hWeak haVars haχ hTheoryFresh hχIns

/--
Maximal Lindenbaum members are deductively closed, assuming list-context completeness.
-/
lemma closed_of_maximal_via_complete
    {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)}
    (hWeak :
      ∀ {Γ Δ : List (Formula σ)} {φ : Formula σ},
        Derives (σ := σ) Γ φ →
        Γ ⊆ Δ →
        Derives (σ := σ) Δ φ)
    (hMF : M ∈ Family (σ := σ) S χ)
    (hMax : Maximal (· ∈ Family (σ := σ) S χ) M) :
    ∀ θ : Formula σ, Derivable (σ := σ) M θ → θ ∈ M := by
  intro θ hDerθ
  by_contra hθNot
  have hCons : Consistent (σ := σ) M := hMF.1
  have hNoχ : ¬ Derivable (σ := σ) M χ := hMF.2.2
  have hConsIns : Consistent (σ := σ) (Set.insert θ M) := by
    intro hBotIns
    have hBot : Derivable (σ := σ) M (.bot : Formula σ) :=
      derivable_of_insert_of_derivable (σ := σ) (T := M) (θ := θ) (χ := (.bot : Formula σ))
        hWeak hDerθ hBotIns
    exact hCons hBot
  have hNoχIns : ¬ Derivable (σ := σ) (Set.insert θ M) χ := by
    intro hχIns
    have hχ : Derivable (σ := σ) M χ :=
      derivable_of_insert_of_derivable (σ := σ) (T := M) (θ := θ) (χ := χ)
        hWeak hDerθ hχIns
    exact hNoχ hχ
  have hFamIns : Set.insert θ M ∈ Family (σ := σ) S χ := by
    refine ⟨hConsIns, ?_, hNoχIns⟩
    intro t ht
    exact Or.inr ((hMF.2.1) ht)
  have hSub : M ⊆ Set.insert θ M := by
    intro t ht
    exact Or.inr ht
  have hEq : Set.insert θ M = M := (hMax.eq_of_subset hFamIns hSub).symm
  have : θ ∈ M := by
    have : θ ∈ Set.insert θ M := Or.inl rfl
    simpa [hEq] using this
  exact hθNot this

/--
Sentence-restricted closure for maximal sentence-family members.

This is the sentence counterpart of `closed_of_maximal_via_complete`:
if `θ` is a closed formula derivable from `M`, then `θ ∈ M`.
-/
lemma closed_sentence_of_maximal_sentence_via_complete
    {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)}
    (hWeak :
      ∀ {Γ Δ : List (Formula σ)} {φ : Formula σ},
        Derives (σ := σ) Γ φ →
        Γ ⊆ Δ →
        Derives (σ := σ) Δ φ)
    (hMF : M ∈ SentenceFamily (σ := σ) S χ)
    (hMax : Maximal (· ∈ SentenceFamily (σ := σ) S χ) M) :
    ∀ θ : Formula σ,
      Syntax.fvFormula (σ := σ) θ = ∅ →
      Derivable (σ := σ) M θ →
      θ ∈ M := by
  intro θ hθClosed hDerθ
  by_contra hθNot
  have hCons : Consistent (σ := σ) M := hMF.1.1
  have hNoχ : ¬ Derivable (σ := σ) M χ := hMF.1.2.2
  have hMClosed : SentenceClosed (σ := σ) M := hMF.2
  have hConsIns : Consistent (σ := σ) (Set.insert θ M) := by
    intro hBotIns
    have hBot : Derivable (σ := σ) M (.bot : Formula σ) :=
      derivable_of_insert_of_derivable (σ := σ) (T := M) (θ := θ) (χ := (.bot : Formula σ))
        hWeak hDerθ hBotIns
    exact hCons hBot
  have hNoχIns : ¬ Derivable (σ := σ) (Set.insert θ M) χ := by
    intro hχIns
    have hχ : Derivable (σ := σ) M χ :=
      derivable_of_insert_of_derivable (σ := σ) (T := M) (θ := θ) (χ := χ)
        hWeak hDerθ hχIns
    exact hNoχ hχ
  have hInsClosed : SentenceClosed (σ := σ) (Set.insert θ M) := by
    intro ψ hψ
    rcases hψ with rfl | hψM
    · exact hθClosed
    · exact hMClosed ψ hψM
  have hFamIns : Set.insert θ M ∈ SentenceFamily (σ := σ) S χ := by
    refine ⟨?_, hInsClosed⟩
    refine ⟨hConsIns, ?_, hNoχIns⟩
    intro t ht
    exact Or.inr ((hMF.1.2.1) ht)
  have hSub : M ⊆ Set.insert θ M := by
    intro t ht
    exact Or.inr ht
  have hEq : Set.insert θ M = M := (hMax.eq_of_subset hFamIns hSub).symm
  have : θ ∈ M := by
    have : θ ∈ Set.insert θ M := Or.inl rfl
    simpa [hEq] using this
  exact hθNot this

/--
Maximal Lindenbaum members satisfy the disjunction property, assuming unrestricted weakening.
-/
lemma prime_of_maximal_via_complete
    {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)}
    (hWeak :
      ∀ {Γ Δ : List (Formula σ)} {φ : Formula σ},
        Derives (σ := σ) Γ φ →
        Γ ⊆ Δ →
        Derives (σ := σ) Δ φ)
    (hMF : M ∈ Family (σ := σ) S χ)
    (hMax : Maximal (· ∈ Family (σ := σ) S χ) M) :
    ∀ φ ψ : Formula σ, (.or φ ψ) ∈ M → φ ∈ M ∨ ψ ∈ M := by
  intro φ ψ hOrMem
  by_contra hNotPrime
  have hφNot : φ ∉ M := by
    intro hφMem
    exact hNotPrime (Or.inl hφMem)
  have hψNot : ψ ∉ M := by
    intro hψMem
    exact hNotPrime (Or.inr hψMem)

  have hDerIns (th : Formula σ) (hth : th ∉ M) :
      Derivable (σ := σ) (Set.insert th M) χ := by
    have hNotFamIns : Set.insert th M ∉ Family (σ := σ) S χ := by
      intro hFamIns
      have hSub : M ⊆ Set.insert th M := by
        intro t ht
        exact Or.inr ht
      have hEq : Set.insert th M = M := (hMax.eq_of_subset hFamIns hSub).symm
      exact hth (by
        have : th ∈ Set.insert th M := Or.inl rfl
        simpa [hEq] using this)
    exact derivable_chi_of_not_family (σ := σ) (S := S) (χ := χ) (M := M)
      hMF hNotFamIns

  have hImpFrom (th : Formula σ) (hth : th ∉ M) :
      Derivable (σ := σ) M (.imp th χ) :=
    derivable_imp_of_derivable_insert (σ := σ) (T := M) (θ := th) (χ := χ)
      hWeak (hDerIns th hth)

  rcases hImpFrom φ hφNot with ⟨Γφ, hΓφM, hDerImpφ⟩
  rcases hImpFrom ψ hψNot with ⟨Γψ, hΓψM, hDerImpψ⟩
  let Δ : List (Formula σ) := .or φ ψ :: (Γφ ++ Γψ)
  have hDerOr : Derives (σ := σ) Δ (.or φ ψ) := Derives.hyp (by simp [Δ])
  have hDerImpφΔ : Derives (σ := σ) Δ (.imp φ χ) :=
    hWeak hDerImpφ (by
      intro θ hθ
      have hθ' : θ ∈ Γφ ++ Γψ := List.mem_append_left _ hθ
      simpa [Δ] using List.mem_cons_of_mem (.or φ ψ) hθ')
  have hDerImpψΔ : Derives (σ := σ) Δ (.imp ψ χ) :=
    hWeak hDerImpψ (by
      intro θ hθ
      have hθ' : θ ∈ Γφ ++ Γψ := List.mem_append_right _ hθ
      simpa [Δ] using List.mem_cons_of_mem (.or φ ψ) hθ')
  have hDerLeft : Derives (σ := σ) (φ :: Δ) χ := by
    have hDerImpφLeft : Derives (σ := σ) (φ :: Δ) (.imp φ χ) :=
      hWeak hDerImpφΔ (by
        intro θ hθ
        exact List.mem_cons_of_mem _ hθ)
    have hDerφLeft : Derives (σ := σ) (φ :: Δ) φ :=
      Derives.hyp (by simp)
    exact Derives.impE hDerImpφLeft hDerφLeft
  have hDerRight : Derives (σ := σ) (ψ :: Δ) χ := by
    have hDerImpψRight : Derives (σ := σ) (ψ :: Δ) (.imp ψ χ) :=
      hWeak hDerImpψΔ (by
        intro θ hθ
        exact List.mem_cons_of_mem _ hθ)
    have hDerψRight : Derives (σ := σ) (ψ :: Δ) ψ :=
      Derives.hyp (by simp)
    exact Derives.impE hDerImpψRight hDerψRight
  have hDerCtxχ : Derives (σ := σ) Δ χ :=
    Derives.orE hDerOr hDerLeft hDerRight
  have hDerivMχ : Derivable (σ := σ) M χ := by
    refine ⟨Δ, ?_, hDerCtxχ⟩
    intro t ht
    simp [Δ, List.mem_append] at ht
    rcases ht with rfl | ht | ht
    · exact hOrMem
    · exact hΓφM t ht
    · exact hΓψM t ht
  exact hMF.2.2 hDerivMχ

/--
Sentence-restricted disjunction property for maximal sentence-family members.

If `(φ ∨ ψ)` is closed and belongs to `M`, then one of the disjuncts belongs to `M`.
-/
lemma prime_sentence_of_maximal_sentence_via_complete
    {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)}
    (hWeak :
      ∀ {Γ Δ : List (Formula σ)} {φ : Formula σ},
        Derives (σ := σ) Γ φ →
        Γ ⊆ Δ →
        Derives (σ := σ) Δ φ)
    (hMF : M ∈ SentenceFamily (σ := σ) S χ)
    (hMax : Maximal (· ∈ SentenceFamily (σ := σ) S χ) M) :
    ∀ φ ψ : Formula σ,
      Syntax.fvFormula (σ := σ) (.or φ ψ) = ∅ →
      (.or φ ψ) ∈ M →
      φ ∈ M ∨ ψ ∈ M := by
  intro φ ψ hOrClosed hOrMem
  by_contra hNotPrime
  have hφNot : φ ∉ M := by
    intro hφMem
    exact hNotPrime (Or.inl hφMem)
  have hψNot : ψ ∉ M := by
    intro hψMem
    exact hNotPrime (Or.inr hψMem)
  have hMClosed : SentenceClosed (σ := σ) M := hMF.2
  have hFvSplit :
      Syntax.fvFormula (σ := σ) φ ∪ Syntax.fvFormula (σ := σ) ψ = ∅ := by
    simpa [Syntax.fvFormula] using hOrClosed
  have hφClosed : Syntax.fvFormula (σ := σ) φ = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.2
    intro a ha
    have hNotUnion : a ∉ Syntax.fvFormula (σ := σ) φ ∪ Syntax.fvFormula (σ := σ) ψ := by
      simp [hFvSplit]
    exact hNotUnion (Finset.mem_union.2 (Or.inl ha))
  have hψClosed : Syntax.fvFormula (σ := σ) ψ = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.2
    intro a ha
    have hNotUnion : a ∉ Syntax.fvFormula (σ := σ) φ ∪ Syntax.fvFormula (σ := σ) ψ := by
      simp [hFvSplit]
    exact hNotUnion (Finset.mem_union.2 (Or.inr ha))

  have hDerIns (th : Formula σ) (hth : th ∉ M) (hthClosed : Syntax.fvFormula (σ := σ) th = ∅) :
      Derivable (σ := σ) (Set.insert th M) χ := by
    have hNotFamInsSentence : Set.insert th M ∉ SentenceFamily (σ := σ) S χ := by
      intro hFamIns
      have hSub : M ⊆ Set.insert th M := by
        intro t ht
        exact Or.inr ht
      have hEq : Set.insert th M = M := (hMax.eq_of_subset hFamIns hSub).symm
      exact hth (by
        have : th ∈ Set.insert th M := Or.inl rfl
        simpa [hEq] using this)
    have hNotFamIns : Set.insert th M ∉ Family (σ := σ) S χ := by
      intro hFamIns
      have hInsClosed : SentenceClosed (σ := σ) (Set.insert th M) := by
        intro ξ hξ
        rcases hξ with rfl | hξM
        · exact hthClosed
        · exact hMClosed ξ hξM
      exact hNotFamInsSentence ⟨hFamIns, hInsClosed⟩
    exact derivable_chi_of_not_family
      (σ := σ) (S := S) (χ := χ) (M := M) (θ := th)
      hMF.1 hNotFamIns

  have hImpFrom (th : Formula σ) (hth : th ∉ M) (hthClosed : Syntax.fvFormula (σ := σ) th = ∅) :
      Derivable (σ := σ) M (.imp th χ) :=
    derivable_imp_of_derivable_insert (σ := σ) (T := M) (θ := th) (χ := χ)
      hWeak (hDerIns th hth hthClosed)

  rcases hImpFrom φ hφNot hφClosed with ⟨Γφ, hΓφM, hDerImpφ⟩
  rcases hImpFrom ψ hψNot hψClosed with ⟨Γψ, hΓψM, hDerImpψ⟩
  let Δ : List (Formula σ) := .or φ ψ :: (Γφ ++ Γψ)
  have hDerOr : Derives (σ := σ) Δ (.or φ ψ) := Derives.hyp (by simp [Δ])
  have hDerImpφΔ : Derives (σ := σ) Δ (.imp φ χ) :=
    hWeak hDerImpφ (by
      intro θ hθ
      have hθ' : θ ∈ Γφ ++ Γψ := List.mem_append_left _ hθ
      simpa [Δ] using List.mem_cons_of_mem (.or φ ψ) hθ')
  have hDerImpψΔ : Derives (σ := σ) Δ (.imp ψ χ) :=
    hWeak hDerImpψ (by
      intro θ hθ
      have hθ' : θ ∈ Γφ ++ Γψ := List.mem_append_right _ hθ
      simpa [Δ] using List.mem_cons_of_mem (.or φ ψ) hθ')
  have hDerLeft : Derives (σ := σ) (φ :: Δ) χ := by
    have hDerImpφLeft : Derives (σ := σ) (φ :: Δ) (.imp φ χ) :=
      hWeak hDerImpφΔ (by
        intro θ hθ
        exact List.mem_cons_of_mem _ hθ)
    have hDerφLeft : Derives (σ := σ) (φ :: Δ) φ :=
      Derives.hyp (by simp)
    exact Derives.impE hDerImpφLeft hDerφLeft
  have hDerRight : Derives (σ := σ) (ψ :: Δ) χ := by
    have hDerImpψRight : Derives (σ := σ) (ψ :: Δ) (.imp ψ χ) :=
      hWeak hDerImpψΔ (by
        intro θ hθ
        exact List.mem_cons_of_mem _ hθ)
    have hDerψRight : Derives (σ := σ) (ψ :: Δ) ψ :=
      Derives.hyp (by simp)
    exact Derives.impE hDerImpψRight hDerψRight
  have hDerCtxχ : Derives (σ := σ) Δ χ :=
    Derives.orE hDerOr hDerLeft hDerRight
  have hDerivMχ : Derivable (σ := σ) M χ := by
    refine ⟨Δ, ?_, hDerCtxχ⟩
    intro θ hθ
    simp [Δ, List.mem_append] at hθ
    rcases hθ with rfl | ht | ht
    · exact hOrMem
    · exact hΓφM θ ht
    · exact hΓψM θ ht
  exact hMF.1.2.2 hDerivMχ

end Lindenbaum

/-! ### Sentence-world shell over maximal sentence-family members -/

/--
Sentence-focused canonical world data extracted from a maximal sentence-family member.

This keeps only the closure/prime facts that are currently available internally on the
sentence-restricted route.
-/
structure SentenceWorld (σ : Type) where
  carrier : Set (Formula σ)
  consistent : Consistent (σ := σ) carrier
  closedSentence : Lindenbaum.SentenceClosed (σ := σ) carrier
  closedDeriv :
    ∀ θ : Formula σ,
      Syntax.fvFormula (σ := σ) θ = ∅ →
      Derivable (σ := σ) carrier θ →
      θ ∈ carrier
  primeSentence :
    ∀ φ ψ : Formula σ,
      Syntax.fvFormula (σ := σ) (.or φ ψ) = ∅ →
      (.or φ ψ) ∈ carrier →
      φ ∈ carrier ∨ ψ ∈ carrier

instance : LE (SentenceWorld σ) := ⟨fun w v => w.carrier ⊆ v.carrier⟩

instance : Preorder (SentenceWorld σ) where
  le := (· ≤ ·)
  le_refl _ := by
    exact subset_rfl
  le_trans _ _ _ h1 h2 := by
    exact Set.Subset.trans h1 h2

namespace SentenceWorld

variable (σ : Type)

def ofMaximalSentence
    (hWeak :
      ∀ {Γ Δ : List (Formula σ)} {φ : Formula σ},
        Derives (σ := σ) Γ φ →
        Γ ⊆ Δ →
        Derives (σ := σ) Δ φ)
    {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)}
    (hMF : M ∈ Lindenbaum.SentenceFamily (σ := σ) S χ)
    (hMax : Maximal (· ∈ Lindenbaum.SentenceFamily (σ := σ) S χ) M) :
    SentenceWorld σ where
  carrier := M
  consistent := hMF.1.1
  closedSentence := hMF.2
  closedDeriv :=
    Lindenbaum.closed_sentence_of_maximal_sentence_via_complete
      (σ := σ) hWeak hMF hMax
  primeSentence :=
    Lindenbaum.prime_sentence_of_maximal_sentence_via_complete
      (σ := σ) hWeak hMF hMax

@[simp] lemma carrier_ofMaximalSentence
    (hWeak :
      ∀ {Γ Δ : List (Formula σ)} {φ : Formula σ},
        Derives (σ := σ) Γ φ →
        Γ ⊆ Δ →
        Derives (σ := σ) Δ φ)
    {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)}
    (hMF : M ∈ Lindenbaum.SentenceFamily (σ := σ) S χ)
    (hMax : Maximal (· ∈ Lindenbaum.SentenceFamily (σ := σ) S χ) M) :
    (ofMaximalSentence (σ := σ) hWeak hMF hMax).carrier = M := rfl

end SentenceWorld

/-- Canonical first-order model shell (domain `Var`) on sentence worlds. -/
def sentenceCanonicalModel : Model (SentenceWorld σ) σ Var where
  valPred w p args := (.pred p (args.map Term.var) : Formula σ) ∈ w.carrier
  monoPred := by
    intro w v hwv p args h
    exact hwv h
  valEx w d := (.eExists (.var d) : Formula σ) ∈ w.carrier
  monoEx := by
    intro w v hwv d h
    exact hwv h

/-- Identity valuation over the sentence-world canonical `Var` domain. -/
def sentenceIdVarValuation : Valuation Var := fun x => x

@[simp] theorem evalTerm_sentenceIdVarValuation (t : Term) :
    evalTerm sentenceIdVarValuation t = (match t with | .var x => x) := by
  cases t
  rfl

@[simp] theorem sentence_forces_pred_iff_mem
    (w : SentenceWorld σ) (p : σ) (args : List Term) :
    Forces sentenceCanonicalModel sentenceIdVarValuation w (.pred p args) ↔
      (.pred p args : Formula σ) ∈ w.carrier := by
  have hMap : (args.map (evalTerm sentenceIdVarValuation)).map Term.var = args := by
    induction args with
    | nil =>
        rfl
    | cons t ts ih =>
        cases t with
        | var x =>
            simp [evalTerm, sentenceIdVarValuation, ih]
  change
      (.pred p ((args.map (evalTerm sentenceIdVarValuation)).map Term.var) : Formula σ) ∈
        w.carrier ↔
      (.pred p args : Formula σ) ∈ w.carrier
  simp [hMap]

@[simp] theorem sentence_forces_exists_atom_iff_mem
    (w : SentenceWorld σ) (t : Term) :
    Forces sentenceCanonicalModel sentenceIdVarValuation w (.eExists t) ↔
      (.eExists t : Formula σ) ∈ w.carrier := by
  cases t with
  | var x =>
      change (.eExists (.var (evalTerm sentenceIdVarValuation (.var x))) : Formula σ) ∈ w.carrier ↔
        (.eExists (.var x) : Formula σ) ∈ w.carrier
      simp

@[simp] theorem sentence_forces_top_iff_mem
    (w : SentenceWorld σ)
    (hClosedDeriv :
      ∀ θ : Formula σ,
        Syntax.fvFormula (σ := σ) θ = ∅ →
        Derivable (σ := σ) w.carrier θ →
        θ ∈ w.carrier) :
    Forces sentenceCanonicalModel sentenceIdVarValuation w (.top : Formula σ) ↔
      (.top : Formula σ) ∈ w.carrier := by
  constructor
  · intro _
    have hDer : Derivable (σ := σ) w.carrier (.top : Formula σ) :=
      ⟨[], by simp, Derives.topI⟩
    exact hClosedDeriv _ (by simp [Syntax.fvFormula]) hDer
  · intro _
    trivial

@[simp] theorem sentence_forces_bot_iff_mem
    (w : SentenceWorld σ) :
    Forces sentenceCanonicalModel sentenceIdVarValuation w (.bot : Formula σ) ↔
      (.bot : Formula σ) ∈ w.carrier := by
  constructor
  · intro h
    exact False.elim h
  · intro hMem
    exact (w.consistent (derivable_of_mem (σ := σ) (T := w.carrier) hMem)).elim

/--
Sentence-world conjunction truth from subformula truth, using sentence-closure for
the constructor/eliminator derivations.
-/
theorem sentence_forces_and_iff_mem_of
    (w : SentenceWorld σ) {φ ψ : Formula σ}
    (hClosedDeriv :
      ∀ θ : Formula σ,
        Syntax.fvFormula (σ := σ) θ = ∅ →
        Derivable (σ := σ) w.carrier θ →
        θ ∈ w.carrier)
    (hφClosed : Syntax.fvFormula (σ := σ) φ = ∅)
    (hψClosed : Syntax.fvFormula (σ := σ) ψ = ∅)
    (hφ : Forces sentenceCanonicalModel sentenceIdVarValuation w φ ↔ φ ∈ w.carrier)
    (hψ : Forces sentenceCanonicalModel sentenceIdVarValuation w ψ ↔ ψ ∈ w.carrier) :
    Forces sentenceCanonicalModel sentenceIdVarValuation w (.and φ ψ) ↔
      (.and φ ψ : Formula σ) ∈ w.carrier := by
  have hAndClosed : Syntax.fvFormula (σ := σ) (.and φ ψ) = ∅ := by
    simp [Syntax.fvFormula, hφClosed, hψClosed]
  constructor
  · intro hAnd
    have hφMem : φ ∈ w.carrier := hφ.1 hAnd.1
    have hψMem : ψ ∈ w.carrier := hψ.1 hAnd.2
    have hDer : Derivable (σ := σ) w.carrier (.and φ ψ) := by
      refine ⟨[φ, ψ], ?_, ?_⟩
      · intro t ht
        simp at ht
        rcases ht with rfl | rfl
        · exact hφMem
        · exact hψMem
      · exact Derives.andI (Derives.hyp (by simp)) (Derives.hyp (by simp))
    exact hClosedDeriv _ hAndClosed hDer
  · intro hAndMem
    have hφMem : φ ∈ w.carrier := by
      rcases derivable_of_mem (σ := σ) (T := w.carrier) hAndMem with ⟨Γ, hΓ, hDer⟩
      exact hClosedDeriv _ hφClosed ⟨Γ, hΓ, Derives.andEL hDer⟩
    have hψMem : ψ ∈ w.carrier := by
      rcases derivable_of_mem (σ := σ) (T := w.carrier) hAndMem with ⟨Γ, hΓ, hDer⟩
      exact hClosedDeriv _ hψClosed ⟨Γ, hΓ, Derives.andER hDer⟩
    exact And.intro (hφ.2 hφMem) (hψ.2 hψMem)

/--
Sentence-world disjunction truth from subformula truth, using sentence-primality.
-/
theorem sentence_forces_or_iff_mem_of
    (w : SentenceWorld σ) {φ ψ : Formula σ}
    (hClosedDeriv :
      ∀ θ : Formula σ,
        Syntax.fvFormula (σ := σ) θ = ∅ →
        Derivable (σ := σ) w.carrier θ →
        θ ∈ w.carrier)
    (hφClosed : Syntax.fvFormula (σ := σ) φ = ∅)
    (hψClosed : Syntax.fvFormula (σ := σ) ψ = ∅)
    (hφ : Forces sentenceCanonicalModel sentenceIdVarValuation w φ ↔ φ ∈ w.carrier)
    (hψ : Forces sentenceCanonicalModel sentenceIdVarValuation w ψ ↔ ψ ∈ w.carrier) :
    Forces sentenceCanonicalModel sentenceIdVarValuation w (.or φ ψ) ↔
      (.or φ ψ : Formula σ) ∈ w.carrier := by
  have hOrClosed : Syntax.fvFormula (σ := σ) (.or φ ψ) = ∅ := by
    simp [Syntax.fvFormula, hφClosed, hψClosed]
  constructor
  · intro hOr
    cases hOr with
    | inl hForce =>
        have hφMem : φ ∈ w.carrier := hφ.1 hForce
        have hDer : Derivable (σ := σ) w.carrier (.or φ ψ) := by
          refine ⟨[φ], ?_, ?_⟩
          · intro t ht
            simp at ht
            subst ht
            exact hφMem
          · exact Derives.orIL (Derives.hyp (by simp))
        exact hClosedDeriv _ hOrClosed hDer
    | inr hForce =>
        have hψMem : ψ ∈ w.carrier := hψ.1 hForce
        have hDer : Derivable (σ := σ) w.carrier (.or φ ψ) := by
          refine ⟨[ψ], ?_, ?_⟩
          · intro t ht
            simp at ht
            subst ht
            exact hψMem
          · exact Derives.orIR (Derives.hyp (by simp))
        exact hClosedDeriv _ hOrClosed hDer
  · intro hOrMem
    rcases w.primeSentence φ ψ hOrClosed hOrMem with hφMem | hψMem
    · exact Or.inl (hφ.2 hφMem)
    · exact Or.inr (hψ.2 hψMem)

/--
Sentence-world negation truth from:
- truth-membership on future worlds for the body;
- a local counterexample extension principle for missing negation-membership.
-/
theorem sentence_forces_not_iff_mem_of
    (w : SentenceWorld σ) {φ : Formula σ}
    (hφ :
      ∀ v : SentenceWorld σ, w ≤ v →
        (Forces sentenceCanonicalModel sentenceIdVarValuation v φ ↔ φ ∈ v.carrier))
    (hNotCounterexample :
      (.not φ : Formula σ) ∉ w.carrier →
        ∃ v : SentenceWorld σ, w ≤ v ∧ φ ∈ v.carrier) :
    Forces sentenceCanonicalModel sentenceIdVarValuation w (.not φ) ↔
      (.not φ : Formula σ) ∈ w.carrier := by
  constructor
  · intro hForce
    by_contra hNotMem
    rcases hNotCounterexample hNotMem with ⟨v, hwv, hφMem⟩
    have hφForce : Forces sentenceCanonicalModel sentenceIdVarValuation v φ :=
      (hφ v hwv).2 hφMem
    exact hForce v hwv hφForce
  · intro hNotMem v hwv hφForce
    have hNotMemV : (.not φ : Formula σ) ∈ v.carrier := hwv hNotMem
    have hφMemV : φ ∈ v.carrier := (hφ v hwv).1 hφForce
    have hBotDer : Derivable (σ := σ) v.carrier (.bot : Formula σ) := by
      refine ⟨[.not φ, φ], ?_, ?_⟩
      · intro t ht
        simp at ht
        rcases ht with rfl | rfl
        · exact hNotMemV
        · exact hφMemV
      ·
        have h1 : Derives (σ := σ) [.not φ, φ] (.not φ) := Derives.hyp (by simp)
        have h2 : Derives (σ := σ) [.not φ, φ] φ := Derives.hyp (by simp)
        exact Derives.notE h1 h2
    exact v.consistent hBotDer

/--
Sentence-world implication truth from:
- truth-membership on future worlds for antecedent and consequent;
- a local counterexample extension principle for missing implication-membership.
-/
theorem sentence_forces_imp_iff_mem_of
    (w : SentenceWorld σ) {φ ψ : Formula σ}
    (hClosedDeriv :
      ∀ v : SentenceWorld σ, w ≤ v →
        ∀ θ : Formula σ,
          Syntax.fvFormula (σ := σ) θ = ∅ →
          Derivable (σ := σ) v.carrier θ →
          θ ∈ v.carrier)
    (hφClosed : Syntax.fvFormula (σ := σ) φ = ∅)
    (hψClosed : Syntax.fvFormula (σ := σ) ψ = ∅)
    (hφ :
      ∀ v : SentenceWorld σ, w ≤ v →
        (Forces sentenceCanonicalModel sentenceIdVarValuation v φ ↔ φ ∈ v.carrier))
    (hψ :
      ∀ v : SentenceWorld σ, w ≤ v →
        (Forces sentenceCanonicalModel sentenceIdVarValuation v ψ ↔ ψ ∈ v.carrier))
    (hImpCounterexample :
      (.imp φ ψ : Formula σ) ∉ w.carrier →
        ∃ v : SentenceWorld σ, w ≤ v ∧ φ ∈ v.carrier ∧ ψ ∉ v.carrier) :
    Forces sentenceCanonicalModel sentenceIdVarValuation w (.imp φ ψ) ↔
      (.imp φ ψ : Formula σ) ∈ w.carrier := by
  constructor
  · intro hForce
    by_contra hImpMem
    rcases hImpCounterexample hImpMem with ⟨v, hwv, hφMem, hψNotMem⟩
    have hφForce : Forces sentenceCanonicalModel sentenceIdVarValuation v φ :=
      (hφ v hwv).2 hφMem
    have hψForce : Forces sentenceCanonicalModel sentenceIdVarValuation v ψ :=
      hForce v hwv hφForce
    exact hψNotMem ((hψ v hwv).1 hψForce)
  · intro hImpMem v hwv hφForce
    have hImpMemV : (.imp φ ψ : Formula σ) ∈ v.carrier := hwv hImpMem
    have hφMemV : φ ∈ v.carrier := (hφ v hwv).1 hφForce
    have hψDer : Derivable (σ := σ) v.carrier ψ := by
      refine ⟨[.imp φ ψ, φ], ?_, ?_⟩
      · intro t ht
        simp at ht
        rcases ht with rfl | rfl
        · exact hImpMemV
        · exact hφMemV
      ·
        have h1 : Derives (σ := σ) [.imp φ ψ, φ] (.imp φ ψ) := Derives.hyp (by simp)
        have h2 : Derives (σ := σ) [.imp φ ψ, φ] φ := Derives.hyp (by simp)
        exact Derives.impE h1 h2
    have hψMemV : ψ ∈ v.carrier := by
      exact hClosedDeriv v hwv ψ hψClosed hψDer
    exact (hψ v hwv).2 hψMemV

/--
Sentence-world existential truth from:
- an internal witness-membership extractor for `sigma` membership,
- body truth-membership on witness instances,
- and the remaining hard converse (`Forces sigma -> membership`).

This isolates the sentence-route `sigma` closure so the unresolved part is explicit.
-/
theorem sentence_forces_sigma_iff_mem_of
    (w : SentenceWorld σ) {x : Var} {φ : Formula σ}
    (hSigmaWitness :
      (.sigma x φ : Formula σ) ∈ w.carrier →
        ∃ a : Var,
          a ∉ Syntax.varsFormula (σ := σ) φ ∧
          Syntax.substFormula (σ := σ) x (.var a) φ ∈ w.carrier)
    (hSubst :
      ∀ a : Var, a ∉ Syntax.varsFormula (σ := σ) φ →
        (Forces sentenceCanonicalModel sentenceIdVarValuation w
            (Syntax.substFormula (σ := σ) x (.var a) φ) ↔
          Syntax.substFormula (σ := σ) x (.var a) φ ∈ w.carrier))
    (hSigmaForcesMem :
      Forces sentenceCanonicalModel sentenceIdVarValuation w (.sigma x φ) →
        (.sigma x φ : Formula σ) ∈ w.carrier) :
    Forces sentenceCanonicalModel sentenceIdVarValuation w (.sigma x φ) ↔
      (.sigma x φ : Formula σ) ∈ w.carrier := by
  constructor
  · intro hForce
    exact hSigmaForcesMem hForce
  · intro hSigmaMem
    rcases hSigmaWitness hSigmaMem with ⟨a, haVars, haMem⟩
    have hSubstForce :
        Forces sentenceCanonicalModel sentenceIdVarValuation w
          (Syntax.substFormula (σ := σ) x (.var a) φ) :=
      (hSubst a haVars).2 haMem
    have hBody :
        Forces sentenceCanonicalModel
          (update sentenceIdVarValuation x (sentenceIdVarValuation a)) w φ :=
      (KripkeFO.forces_substFormula_var_of_not_mem_varsFormula
        (σ := σ)
        (M := sentenceCanonicalModel (σ := σ))
        (ρ := sentenceIdVarValuation)
        (w := w)
        x a φ haVars).1 hSubstForce
    refine ⟨a, ?_⟩
    simpa [sentenceIdVarValuation, update_self] using hBody

/--
Sentence-world universal truth from:
- an internal instantiation-membership extractor for `pi` membership,
- body truth-membership on all instantiated bodies,
- and an explicit substitution-to-body forcing transport.

As with the `sigma` helper above, this isolates the remaining hard converse
(`Forces pi -> membership`) behind a dedicated assumption.
-/
theorem sentence_forces_pi_iff_mem_of
    (w : SentenceWorld σ) {x : Var} {φ : Formula σ}
    (hPiInstance :
      ∀ v : SentenceWorld σ,
        (.pi x φ : Formula σ) ∈ v.carrier →
          ∀ a : Var,
            Syntax.substFormula (σ := σ) x (.var a) φ ∈ v.carrier)
    (hSubst :
      ∀ v : SentenceWorld σ, ∀ a : Var,
        (Forces sentenceCanonicalModel sentenceIdVarValuation v
            (Syntax.substFormula (σ := σ) x (.var a) φ) ↔
          Syntax.substFormula (σ := σ) x (.var a) φ ∈ v.carrier))
    (hSubstBody :
      ∀ v : SentenceWorld σ, ∀ a : Var,
        Forces sentenceCanonicalModel sentenceIdVarValuation v
            (Syntax.substFormula (σ := σ) x (.var a) φ) →
          Forces sentenceCanonicalModel
            (update sentenceIdVarValuation x (sentenceIdVarValuation a)) v φ)
    (hPiForcesMem :
      Forces sentenceCanonicalModel sentenceIdVarValuation w (.pi x φ) →
        (.pi x φ : Formula σ) ∈ w.carrier) :
    Forces sentenceCanonicalModel sentenceIdVarValuation w (.pi x φ) ↔
      (.pi x φ : Formula σ) ∈ w.carrier := by
  constructor
  · intro hForce
    exact hPiForcesMem hForce
  · intro hPiMem v hwv a
    have hPiMemV : (.pi x φ : Formula σ) ∈ v.carrier := hwv hPiMem
    have hSubstForce :
        Forces sentenceCanonicalModel sentenceIdVarValuation v
          (Syntax.substFormula (σ := σ) x (.var a) φ) :=
      (hSubst v a).2 (hPiInstance v hPiMemV a)
    exact hSubstBody v a hSubstForce

/--
Sentence-route obligation: closed derivability implies membership in each sentence world.
-/
class HasSentenceClosedDeriv : Prop where
  closed_deriv :
    ∀ {w : SentenceWorld σ} {θ : Formula σ},
      Syntax.fvFormula (σ := σ) θ = ∅ →
      Derivable (σ := σ) w.carrier θ →
      θ ∈ w.carrier

instance (priority := 100)
    hasSentenceClosedDeriv_of_sentenceWorld :
    HasSentenceClosedDeriv (σ := σ) where
  closed_deriv := by
    intro w θ hθClosed hDer
    exact w.closedDeriv θ hθClosed hDer

/--
Sentence-route obligation: canonical neg/imp counterexample extensions over sentence worlds.
-/
class HasSentenceNegImpExtensions : Prop where
  not_counterexample :
    ∀ {w : SentenceWorld σ} {φ : Formula σ},
      Syntax.fvFormula (σ := σ) φ = ∅ →
      (.not φ : Formula σ) ∉ w.carrier →
        ∃ v : SentenceWorld σ, w ≤ v ∧ φ ∈ v.carrier
  imp_counterexample :
    ∀ {w : SentenceWorld σ} {φ ψ : Formula σ},
      Syntax.fvFormula (σ := σ) φ = ∅ →
      Syntax.fvFormula (σ := σ) ψ = ∅ →
      (.imp φ ψ : Formula σ) ∉ w.carrier →
        ∃ v : SentenceWorld σ, w ≤ v ∧ φ ∈ v.carrier ∧ ψ ∉ v.carrier

instance (priority := 100)
    hasSentenceNegImpExtensions_of_openWeakening
    [HasSentenceClosedDeriv (σ := σ)] :
    HasSentenceNegImpExtensions (σ := σ) where
  not_counterexample := by
    intro w φ hφClosed hNotMem
    let S : Set (Formula σ) := Set.insert φ w.carrier
    have hSCons : Consistent (σ := σ) S := by
      intro hDerBotS
      rcases Lindenbaum.derives_cons_of_derivable_insert
        (σ := σ) (T := w.carrier) (θ := φ) (χ := (.bot : Formula σ))
        (fun {Γ Δ : List (Formula σ)} {θ : Formula σ}
          (hDer : Derives (σ := σ) Γ θ) (hSub : Γ ⊆ Δ) =>
            Derives.wk hDer hSub) hDerBotS with
        ⟨Γ, hΓw, hDerConsBot⟩
      have hDerNotΓ : Derives (σ := σ) Γ (.not φ) :=
        Derives.notI hDerConsBot
      have hDerNotW : Derivable (σ := σ) w.carrier (.not φ) :=
        ⟨Γ, hΓw, hDerNotΓ⟩
      have hNotIn : (.not φ : Formula σ) ∈ w.carrier :=
        HasSentenceClosedDeriv.closed_deriv
          (σ := σ)
          (w := w)
          (θ := .not φ)
          (by simp [Syntax.fvFormula, hφClosed])
          hDerNotW
      exact hNotMem hNotIn
    have hNoBot : ¬ Derivable (σ := σ) S (.bot : Formula σ) := hSCons
    have hSClosed : Lindenbaum.SentenceClosed (σ := σ) S := by
      intro θ hθ
      rcases hθ with rfl | hθw
      · exact hφClosed
      · exact w.closedSentence θ hθw
    rcases Lindenbaum.exists_maximal_sentence
      (σ := σ) (S := S) (χ := (.bot : Formula σ))
      hSCons hNoBot hSClosed with
      ⟨M, hSM, hMax⟩
    have hMF :
        M ∈ Lindenbaum.SentenceFamily (σ := σ) S (.bot : Formula σ) := hMax.prop
    let v : SentenceWorld σ :=
      SentenceWorld.ofMaximalSentence
        (σ := σ)
        (hWeak := fun {Γ Δ : List (Formula σ)} {θ : Formula σ}
          (hDer : Derives (σ := σ) Γ θ) (hSub : Γ ⊆ Δ) =>
            Derives.wk hDer hSub)
        (S := S) (χ := (.bot : Formula σ)) (M := M) hMF hMax
    refine ⟨v, ?_, ?_⟩
    · intro θ hθw
      exact hSM (Or.inr hθw)
    · exact hSM (Or.inl rfl)
  imp_counterexample := by
    intro w φ ψ hφClosed hψClosed hImpNotMem
    let S : Set (Formula σ) := Set.insert φ w.carrier
    have hNoPsi : ¬ Derivable (σ := σ) S ψ := by
      intro hDerPsi
      have hImpDer : Derivable (σ := σ) w.carrier (.imp φ ψ) :=
        Lindenbaum.derivable_imp_of_derivable_insert
          (σ := σ) (T := w.carrier) (θ := φ) (χ := ψ)
          (fun {Γ Δ : List (Formula σ)} {θ : Formula σ}
            (hDer : Derives (σ := σ) Γ θ) (hSub : Γ ⊆ Δ) =>
              Derives.wk hDer hSub) hDerPsi
      have hImpIn : (.imp φ ψ : Formula σ) ∈ w.carrier :=
        HasSentenceClosedDeriv.closed_deriv
          (σ := σ)
          (w := w)
          (θ := .imp φ ψ)
          (by simp [Syntax.fvFormula, hφClosed, hψClosed])
          hImpDer
      exact hImpNotMem hImpIn
    have hSCons : Consistent (σ := σ) S := by
      intro hDerBotS
      have hDerPsi : Derivable (σ := σ) S ψ := by
        rcases hDerBotS with ⟨Γ, hΓS, hDerΓBot⟩
        exact ⟨Γ, hΓS, Derives.botE hDerΓBot⟩
      exact hNoPsi hDerPsi
    have hSClosed : Lindenbaum.SentenceClosed (σ := σ) S := by
      intro θ hθ
      rcases hθ with rfl | hθw
      · exact hφClosed
      · exact w.closedSentence θ hθw
    rcases Lindenbaum.exists_maximal_sentence
      (σ := σ) (S := S) (χ := ψ)
      hSCons hNoPsi hSClosed with
      ⟨M, hSM, hMax⟩
    have hMF : M ∈ Lindenbaum.SentenceFamily (σ := σ) S ψ := hMax.prop
    let v : SentenceWorld σ :=
      SentenceWorld.ofMaximalSentence
        (σ := σ)
        (hWeak := fun {Γ Δ : List (Formula σ)} {θ : Formula σ}
          (hDer : Derives (σ := σ) Γ θ) (hSub : Γ ⊆ Δ) =>
            Derives.wk hDer hSub)
        (S := S) (χ := ψ) (M := M) hMF hMax
    have hψNotIn : ψ ∉ v.carrier :=
      Lindenbaum.goal_not_mem_of_sentenceFamily (σ := σ) hMF
    refine ⟨v, ?_, ?_, hψNotIn⟩
    · intro θ hθw
      exact hSM (Or.inr hθw)
    · exact hSM (Or.inl rfl)

/--
Sentence-route obligation: full quantifier truth on sentence worlds.

This keeps the sentence-countermodel path explicit while the final internal constructors for
`sigma`/`pi` are still being completed.
-/
class HasSentenceQuantifierTruth : Prop where
  sigma_forces_iff_mem :
    ∀ (w : SentenceWorld σ) (x : Var) (φ : Formula σ),
      Forces sentenceCanonicalModel sentenceIdVarValuation w (.sigma x φ) ↔
        (.sigma x φ : Formula σ) ∈ w.carrier
  pi_forces_iff_mem :
    ∀ (w : SentenceWorld σ) (x : Var) (φ : Formula σ),
      Forces sentenceCanonicalModel sentenceIdVarValuation w (.pi x φ) ↔
        (.pi x φ : Formula σ) ∈ w.carrier

/-!
`SentenceWorld` carries only sentence members (`closedSentence`), while `pi` forcing quantifies over
all variable assignments in domain `Var`. If a sentence world contains a formula of shape
`pi x (pred p [x])`, `HasSentenceQuantifierTruth` would force membership of the open atom
`pred p [x]`, contradicting `closedSentence`.
-/
theorem sentence_pi_exists_self_contradiction
    [HasSentenceQuantifierTruth (σ := σ)]
    (w : SentenceWorld σ) (x : Var)
    (hPiMem : (.pi x (.eExists (.var x)) : Formula σ) ∈ w.carrier) :
    False := by
  have hPiForce :
      Forces sentenceCanonicalModel sentenceIdVarValuation w (.pi x (.eExists (.var x))) :=
    (HasSentenceQuantifierTruth.pi_forces_iff_mem (σ := σ) w x (.eExists (.var x))).2 hPiMem
  have hExistsBody :
      Forces sentenceCanonicalModel
        (update sentenceIdVarValuation x (sentenceIdVarValuation x)) w
        (.eExists (.var x)) :=
    hPiForce w (by rfl) x
  have hExistsMem : (.eExists (.var x) : Formula σ) ∈ w.carrier := by
    simpa [Forces, sentenceCanonicalModel, sentenceIdVarValuation, update, evalTerm] using hExistsBody
  have hClosed : Syntax.fvFormula (σ := σ) (.eExists (.var x)) = ∅ :=
    w.closedSentence (.eExists (.var x)) hExistsMem
  have hxFv : x ∈ Syntax.fvFormula (σ := σ) (.eExists (.var x)) := by
    simp [Syntax.fvFormula, Syntax.fvTerm]
  simp [hClosed] at hxFv

theorem sentence_pi_pred_self_contradiction
    [HasSentenceQuantifierTruth (σ := σ)]
    (w : SentenceWorld σ) (p : σ) (x : Var)
    (hPiMem : (.pi x (.pred p [.var x]) : Formula σ) ∈ w.carrier) :
    False := by
  have hPiForce :
      Forces sentenceCanonicalModel sentenceIdVarValuation w (.pi x (.pred p [.var x])) :=
    (HasSentenceQuantifierTruth.pi_forces_iff_mem (σ := σ) w x (.pred p [.var x])).2 hPiMem
  have hPredForce :
      Forces sentenceCanonicalModel sentenceIdVarValuation w (.pred p [.var x]) := by
    have hBody :
        Forces sentenceCanonicalModel
          (update sentenceIdVarValuation x (sentenceIdVarValuation x)) w
          (.pred p [.var x]) :=
      hPiForce w (by rfl) x
    have hBodyMem : (.pred p [.var x] : Formula σ) ∈ w.carrier := by
      simpa [Forces, sentenceCanonicalModel, evalTerm, sentenceIdVarValuation, update] using hBody
    exact (sentence_forces_pred_iff_mem (σ := σ) (w := w) p [.var x]).2 hBodyMem
  have hPredMem : (.pred p [.var x] : Formula σ) ∈ w.carrier :=
    (sentence_forces_pred_iff_mem (σ := σ) (w := w) p [.var x]).1 hPredForce
  have hClosed : Syntax.fvFormula (σ := σ) (.pred p [.var x]) = ∅ :=
    w.closedSentence (.pred p [.var x]) hPredMem
  have hxFv : x ∈ Syntax.fvFormula (σ := σ) (.pred p [.var x]) := by
    change x ∈ Syntax.fvTerms ([Term.var x] : List Term)
    simp [Syntax.fvTerms, Syntax.fvTerm]
  simp [hClosed] at hxFv

theorem not_hasSentenceQuantifierTruth_of_pi_pred_self_member
    (hWitness :
      ∃ (w : SentenceWorld σ) (p : σ) (x : Var),
        (.pi x (.pred p [.var x]) : Formula σ) ∈ w.carrier) :
    ¬ HasSentenceQuantifierTruth (σ := σ) := by
  intro hQuant
  rcases hWitness with ⟨w, p, x, hPiMem⟩
  letI : HasSentenceQuantifierTruth (σ := σ) := hQuant
  exact sentence_pi_pred_self_contradiction
    (σ := σ) (w := w) (p := p) (x := x) hPiMem

/--
`HasSentenceQuantifierTruth` is globally inconsistent.

Witness sentence: `pi x (eExists (.var x))`.
-/
theorem not_hasSentenceQuantifierTruth :
    ¬ HasSentenceQuantifierTruth (σ := σ) := by
  let x : Var := 0
  let θ : Formula σ := (.pi x (.eExists (.var x)) : Formula σ)
  let S : Set (Formula σ) := {θ}
  have hThetaClosed : Syntax.fvFormula (σ := σ) θ = ∅ := by
    simp [θ, Syntax.fvFormula, Syntax.fvTerm]
  have hSClosed : Lindenbaum.SentenceClosed (σ := σ) S := by
    intro ψ hψ
    have hψθ : ψ = θ := by simpa [S] using hψ
    subst hψθ
    exact hThetaClosed
  have hSNoBot : ¬ Derivable (σ := σ) S (.bot : Formula σ) := by
    intro hDerBot
    rcases hDerBot with ⟨Γ, hΓS, hDerΓBot⟩
    let M : Model PUnit σ Var := {
      valPred := fun _ _ _ => True
      monoPred := by
        intro _ _ _ _ _ _
        trivial
      valEx := fun _ _ => True
      monoEx := by intro _ _ _ _ _; trivial
    }
    let ρ : Valuation Var := fun v => v
    have hThetaForce : Forces M ρ PUnit.unit θ := by
      simp [θ, Forces, M]
    have hΓForce : ∀ ψ ∈ Γ, Forces M ρ PUnit.unit ψ := by
      intro ψ hψ
      have hψS : ψ ∈ S := hΓS ψ hψ
      have hψθ : ψ = θ := by simpa [S] using hψS
      simpa [hψθ] using hThetaForce
    have hBotForce : Forces M ρ PUnit.unit (.bot : Formula σ) :=
      KripkeFO.soundness (σ := σ) hDerΓBot
        (W := PUnit) (D := Var) (M := M) (ρ := ρ) (w := PUnit.unit) hΓForce
    exact hBotForce
  have hSCons : Consistent (σ := σ) S := hSNoBot
  rcases Lindenbaum.exists_maximal_sentence
    (σ := σ) (S := S) (χ := (.bot : Formula σ))
    hSCons hSNoBot hSClosed with
    ⟨Mmax, hSM, hMax⟩
  have hMF : Mmax ∈ Lindenbaum.SentenceFamily (σ := σ) S (.bot : Formula σ) := hMax.prop
  let w : SentenceWorld σ :=
    SentenceWorld.ofMaximalSentence
      (σ := σ)
      (hWeak := fun {Γ Δ : List (Formula σ)} {φ : Formula σ}
        (hDer : Derives (σ := σ) Γ φ) (hSub : Γ ⊆ Δ) =>
          Derives.wk hDer hSub)
      (hMF := hMF)
      (hMax := hMax)
  have hThetaMem : θ ∈ w.carrier := hSM (by simp [S])
  intro hQuant
  letI : HasSentenceQuantifierTruth (σ := σ) := hQuant
  exact sentence_pi_exists_self_contradiction (σ := σ) (w := w) (x := x) hThetaMem

/--
`HasSentenceQuantifierTruth` is inconsistent whenever the predicate signature is inhabited.

Sketch:
1. start from the singleton sentence theory `{pi x (pred p [x])}`;
2. show it is sentence-closed and consistent (via Kripke soundness in a trivial always-true model);
3. extract a maximal sentence-family member containing that sentence;
4. apply `not_hasSentenceQuantifierTruth_of_pi_pred_self_member`.
-/
theorem not_hasSentenceQuantifierTruth_of_nonempty
    [Nonempty σ] :
    ¬ HasSentenceQuantifierTruth (σ := σ) := by
  exact not_hasSentenceQuantifierTruth (σ := σ)

/--
Closed-formula sentence truth lemma from explicit sentence-route obligations.

This theorem is fully internal for propositional constructors; quantifier cases are delegated to
`HasSentenceQuantifierTruth`.
-/
theorem sentence_truth_iff_mem_closed_of_obligations
    [HasSentenceClosedDeriv (σ := σ)]
    [HasSentenceNegImpExtensions (σ := σ)]
    [HasSentenceQuantifierTruth (σ := σ)] :
    ∀ (w : SentenceWorld σ) (ψ : Formula σ),
      Syntax.fvFormula (σ := σ) ψ = ∅ →
        (Forces sentenceCanonicalModel sentenceIdVarValuation w ψ ↔ ψ ∈ w.carrier) := by
  intro w ψ hClosed
  induction ψ generalizing w with
  | top =>
      exact sentence_forces_top_iff_mem
        (σ := σ)
        (w := w)
        (hClosedDeriv := by
          intro θ hθClosed hDer
          exact HasSentenceClosedDeriv.closed_deriv (σ := σ) (w := w) hθClosed hDer)
  | bot =>
      exact sentence_forces_bot_iff_mem (σ := σ) (w := w)
  | pred p args =>
      exact sentence_forces_pred_iff_mem (σ := σ) (w := w) p args
  | eExists t =>
      exact sentence_forces_exists_atom_iff_mem (σ := σ) (w := w) t
  | not φ ih =>
      have hφClosed : Syntax.fvFormula (σ := σ) φ = ∅ := by
        simpa [Syntax.fvFormula] using hClosed
      exact sentence_forces_not_iff_mem_of
        (σ := σ)
        (w := w)
        (hφ := by
          intro v hwv
          exact ih (w := v) hφClosed)
        (hNotCounterexample := by
          intro hNotMem
          exact HasSentenceNegImpExtensions.not_counterexample
            (σ := σ) (w := w) (φ := φ) hφClosed hNotMem)
  | and φ χ ihφ ihχ =>
      have hSplit :
          Syntax.fvFormula (σ := σ) φ ∪ Syntax.fvFormula (σ := σ) χ = ∅ := by
        simpa [Syntax.fvFormula] using hClosed
      have hφClosed : Syntax.fvFormula (σ := σ) φ = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.2
        intro a ha
        have hNotUnion : a ∉ Syntax.fvFormula (σ := σ) φ ∪ Syntax.fvFormula (σ := σ) χ := by
          simp [hSplit]
        exact hNotUnion (Finset.mem_union.2 (Or.inl ha))
      have hχClosed : Syntax.fvFormula (σ := σ) χ = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.2
        intro a ha
        have hNotUnion : a ∉ Syntax.fvFormula (σ := σ) φ ∪ Syntax.fvFormula (σ := σ) χ := by
          simp [hSplit]
        exact hNotUnion (Finset.mem_union.2 (Or.inr ha))
      exact sentence_forces_and_iff_mem_of
        (σ := σ)
        (w := w)
        (hClosedDeriv := by
          intro θ hθClosed hDer
          exact HasSentenceClosedDeriv.closed_deriv (σ := σ) (w := w) hθClosed hDer)
        (hφClosed := hφClosed)
        (hψClosed := hχClosed)
        (hφ := ihφ (w := w) hφClosed)
        (hψ := ihχ (w := w) hχClosed)
  | or φ χ ihφ ihχ =>
      have hSplit :
          Syntax.fvFormula (σ := σ) φ ∪ Syntax.fvFormula (σ := σ) χ = ∅ := by
        simpa [Syntax.fvFormula] using hClosed
      have hφClosed : Syntax.fvFormula (σ := σ) φ = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.2
        intro a ha
        have hNotUnion : a ∉ Syntax.fvFormula (σ := σ) φ ∪ Syntax.fvFormula (σ := σ) χ := by
          simp [hSplit]
        exact hNotUnion (Finset.mem_union.2 (Or.inl ha))
      have hχClosed : Syntax.fvFormula (σ := σ) χ = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.2
        intro a ha
        have hNotUnion : a ∉ Syntax.fvFormula (σ := σ) φ ∪ Syntax.fvFormula (σ := σ) χ := by
          simp [hSplit]
        exact hNotUnion (Finset.mem_union.2 (Or.inr ha))
      exact sentence_forces_or_iff_mem_of
        (σ := σ)
        (w := w)
        (hClosedDeriv := by
          intro θ hθClosed hDer
          exact HasSentenceClosedDeriv.closed_deriv (σ := σ) (w := w) hθClosed hDer)
        (hφClosed := hφClosed)
        (hψClosed := hχClosed)
        (hφ := ihφ (w := w) hφClosed)
        (hψ := ihχ (w := w) hχClosed)
  | imp φ χ ihφ ihχ =>
      have hSplit :
          Syntax.fvFormula (σ := σ) φ ∪ Syntax.fvFormula (σ := σ) χ = ∅ := by
        simpa [Syntax.fvFormula] using hClosed
      have hφClosed : Syntax.fvFormula (σ := σ) φ = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.2
        intro a ha
        have hNotUnion : a ∉ Syntax.fvFormula (σ := σ) φ ∪ Syntax.fvFormula (σ := σ) χ := by
          simp [hSplit]
        exact hNotUnion (Finset.mem_union.2 (Or.inl ha))
      have hχClosed : Syntax.fvFormula (σ := σ) χ = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.2
        intro a ha
        have hNotUnion : a ∉ Syntax.fvFormula (σ := σ) φ ∪ Syntax.fvFormula (σ := σ) χ := by
          simp [hSplit]
        exact hNotUnion (Finset.mem_union.2 (Or.inr ha))
      exact sentence_forces_imp_iff_mem_of
        (σ := σ)
        (w := w)
        (hClosedDeriv := by
          intro v _hwv θ hθClosed hDer
          exact HasSentenceClosedDeriv.closed_deriv (σ := σ) (w := v) hθClosed hDer)
        (hφClosed := hφClosed)
        (hψClosed := hχClosed)
        (hφ := by
          intro v hwv
          exact ihφ (w := v) hφClosed)
        (hψ := by
          intro v hwv
          exact ihχ (w := v) hχClosed)
        (hImpCounterexample := by
          intro hImpMem
          exact HasSentenceNegImpExtensions.imp_counterexample
            (σ := σ) (w := w) (φ := φ) (ψ := χ) hφClosed hχClosed hImpMem)
  | sigma x φ ih =>
      exact HasSentenceQuantifierTruth.sigma_forces_iff_mem (σ := σ) w x φ
  | pi x φ ih =>
      exact HasSentenceQuantifierTruth.pi_forces_iff_mem (σ := σ) w x φ

/--
Prime + closed + quantifier-saturated theory shape used by the internal canonical model.

`henkinSigma` and `henkinPi` capture the witness/instantiation obligations needed for
quantifier cases in the eventual FO truth lemma.
-/
structure SaturatedTheory (σ : Type) where
  carrier : Set (Formula σ)
  consistent : Consistent (σ := σ) carrier
  closed : ∀ φ : Formula σ, Derivable (σ := σ) carrier φ → φ ∈ carrier
  prime : ∀ φ ψ : Formula σ, (.or φ ψ) ∈ carrier → φ ∈ carrier ∨ ψ ∈ carrier
  henkinSigma :
    ∀ x : Var, ∀ φ : Formula σ, (.sigma x φ) ∈ carrier →
      ∃ a : Var,
        a ∉ Syntax.varsFormula (σ := σ) φ ∧
        Syntax.substFormula (σ := σ) x (.var a) φ ∈ carrier
  henkinPi :
    ∀ x : Var, ∀ φ : Formula σ, (.pi x φ) ∈ carrier →
      ∀ a : Var, a ∉ Syntax.boundVars (σ := σ) φ →
        Syntax.substFormula (σ := σ) x (.var a) φ ∈ carrier

namespace SaturatedTheory

variable (w : SaturatedTheory σ)

lemma mem_of_derivable {φ : Formula σ} :
    Derivable (σ := σ) w.carrier φ → φ ∈ w.carrier :=
  w.closed φ

lemma pi_instance_mem_of_not_mem_boundVars {x a : Var} {φ : Formula σ}
    (ha : a ∉ Syntax.boundVars (σ := σ) φ) :
    (.pi x φ) ∈ w.carrier →
      Syntax.substFormula (σ := σ) x (.var a) φ ∈ w.carrier :=
by
  intro hPi
  exact w.henkinPi x φ hPi a ha

lemma pi_instance_mem {x a : Var} {φ : Formula σ}
    (ha : a ∉ Syntax.varsFormula (σ := σ) φ) :
    (.pi x φ) ∈ w.carrier →
      Syntax.substFormula (σ := σ) x (.var a) φ ∈ w.carrier := by
  intro hPi
  exact w.pi_instance_mem_of_not_mem_boundVars
    (x := x) (a := a) (φ := φ)
    (Syntax.not_mem_boundVars_of_not_mem_varsFormula (σ := σ) ha)
    hPi

/--
Unrestricted `pi` instance extraction from membership.

This uses `piE` directly through `closed`, so no side condition on `a` is required.
-/
lemma pi_instance_mem_any {x a : Var} {φ : Formula σ} :
    (.pi x φ) ∈ w.carrier →
      Syntax.substFormula (σ := σ) x (.var a) φ ∈ w.carrier := by
  intro hPi
  have hDerPi : Derivable (σ := σ) w.carrier (.pi x φ) :=
    derivable_of_mem (σ := σ) (T := w.carrier) hPi
  rcases hDerPi with ⟨Γ, hΓ, hDerΓPi⟩
  have hDerSubst : Derivable (σ := σ) w.carrier
      (Syntax.substFormula (σ := σ) x (.var a) φ) := by
    exact ⟨Γ, hΓ, Derives.piE (x := x) (a := a) (φ := φ) hDerΓPi⟩
  exact w.closed _ hDerSubst

lemma sigma_witness_mem {x : Var} {φ : Formula σ} :
    (.sigma x φ) ∈ w.carrier →
      ∃ a : Var,
        a ∉ Syntax.varsFormula (σ := σ) φ ∧
        Syntax.substFormula (σ := σ) x (.var a) φ ∈ w.carrier :=
  w.henkinSigma x φ

end SaturatedTheory

/-! ### Canonical frame/model shell over saturated theories -/

abbrev W : Type := SaturatedTheory σ

instance : LE (W (σ := σ)) := ⟨fun w v => w.carrier ⊆ v.carrier⟩

instance : Preorder (W (σ := σ)) where
  le := (· ≤ ·)
  le_refl _ := by
    exact subset_rfl
  le_trans _ _ _ h1 h2 := by
    exact Set.Subset.trans h1 h2

/-- Canonical first-order model shell (domain `Var`) on saturated theories. -/
def canonicalModel : Model (W (σ := σ)) σ Var where
  valPred w p args := (.pred p (args.map Term.var) : Formula σ) ∈ w.carrier
  monoPred := by
    intro w v hwv p args h
    exact hwv h
  valEx w d := (.eExists (.var d) : Formula σ) ∈ w.carrier
  monoEx := by
    intro w v hwv d h
    exact hwv h

/-- Identity valuation over the canonical `Var` domain. -/
def idVarValuation : Valuation Var := fun x => x

@[simp] theorem evalTerm_idVarValuation (t : Term) :
    evalTerm idVarValuation t = (match t with | .var x => x) := by
  cases t
  rfl

@[simp] theorem canonical_forces_pred_iff_mem
    (w : W (σ := σ)) (p : σ) (args : List Term) :
    Forces (canonicalModel (σ := σ)) idVarValuation w (.pred p args) ↔
      (.pred p args : Formula σ) ∈ w.carrier := by
  have hMap : (args.map (evalTerm idVarValuation)).map Term.var = args := by
    induction args with
    | nil =>
        rfl
    | cons t ts ih =>
        cases t with
        | var x =>
            simp [evalTerm, idVarValuation, ih]
  simp [Forces, canonicalModel, hMap]

@[simp] theorem canonical_forces_exists_atom_iff_mem
    (w : W (σ := σ)) (t : Term) :
    Forces (canonicalModel (σ := σ)) idVarValuation w (.eExists t) ↔
      (.eExists t : Formula σ) ∈ w.carrier := by
  cases t with
  | var x =>
      simp [Forces, canonicalModel, evalTerm, idVarValuation]

/--
Quantifier truth-lemma helper (`sigma`, membership -> forcing).

Given forcing for all needed substitution instances of the body, a Henkin witness in the carrier
produces an actual semantic witness in the canonical model.
-/
lemma canonical_forces_sigma_of_mem
    (w : W (σ := σ)) {x : Var} {φ : Formula σ}
    (hSubst :
      ∀ a : Var,
        a ∉ Syntax.varsFormula (σ := σ) φ →
        Syntax.substFormula (σ := σ) x (.var a) φ ∈ w.carrier →
        Forces (canonicalModel (σ := σ)) idVarValuation w
          (Syntax.substFormula (σ := σ) x (.var a) φ))
    (hSigma : (.sigma x φ : Formula σ) ∈ w.carrier) :
    Forces (canonicalModel (σ := σ)) idVarValuation w (.sigma x φ) := by
  rcases w.sigma_witness_mem (x := x) (φ := φ) hSigma with ⟨a, haVars, haMem⟩
  refine ⟨a, ?_⟩
  have hSubstForces :
      Forces (canonicalModel (σ := σ)) idVarValuation w
        (Syntax.substFormula (σ := σ) x (.var a) φ) :=
    hSubst a haVars haMem
  have hBody :
      Forces (canonicalModel (σ := σ)) (update idVarValuation x (idVarValuation a)) w φ :=
    (KripkeFO.forces_substFormula_var
      (σ := σ)
      (M := canonicalModel (σ := σ))
      (ρ := idVarValuation)
      (w := w)
      x a φ).1 hSubstForces
  simpa [idVarValuation, update_self] using hBody

/--
Quantifier truth helper (`sigma`, membership -> forcing) driven by a smaller-formula truth oracle.

This packages the size argument needed for well-founded canonical truth recursion:
every witness instance `substFormula x (.var a) φ` has strictly smaller `Syntax.fSize` than
`.sigma x φ`.
-/
lemma canonical_forces_sigma_of_mem_of_lt
    (w : W (σ := σ)) {x : Var} {φ : Formula σ}
    (hTruthLt :
      ∀ ψ : Formula σ,
        Syntax.fSize (σ := σ) ψ < Syntax.fSize (σ := σ) (.sigma x φ) →
          (Forces (canonicalModel (σ := σ)) idVarValuation w ψ ↔ ψ ∈ w.carrier))
    (hSigma : (.sigma x φ : Formula σ) ∈ w.carrier) :
    Forces (canonicalModel (σ := σ)) idVarValuation w (.sigma x φ) := by
  refine canonical_forces_sigma_of_mem (σ := σ) (w := w) (x := x) (φ := φ) ?_ hSigma
  intro a haVars haMem
  have hSizeEq :
      Syntax.fSize (σ := σ) (Syntax.substFormula (σ := σ) x (.var a) φ) =
        Syntax.fSize (σ := σ) φ :=
    Syntax.fSize_substFormula_var (x := x) (a := a) φ
  have hSizeLt :
      Syntax.fSize (σ := σ) (Syntax.substFormula (σ := σ) x (.var a) φ) <
        Syntax.fSize (σ := σ) (.sigma x φ) := by
    simp [hSizeEq, Syntax.fSize]
  have hSubstTruthFun :
      Syntax.fSize (σ := σ) (Syntax.substFormula (σ := σ) x (.var a) φ) <
          Syntax.fSize (σ := σ) (.sigma x φ) →
        (Forces (canonicalModel (σ := σ)) idVarValuation w
            (Syntax.substFormula (σ := σ) x (.var a) φ) ↔
          Syntax.substFormula (σ := σ) x (.var a) φ ∈ w.carrier) := by
    exact hTruthLt (Syntax.substFormula (σ := σ) x (.var a) φ)
  have hSubstTruth :
      Forces (canonicalModel (σ := σ)) idVarValuation w
          (Syntax.substFormula (σ := σ) x (.var a) φ) ↔
        Syntax.substFormula (σ := σ) x (.var a) φ ∈ w.carrier :=
    hSubstTruthFun hSizeLt
  exact hSubstTruth.2 haMem

/-- Canonical `sigma` converse (forcing -> membership) via unconditional substitution semantics. -/
lemma canonical_sigma_mem_of_forces_of_lt_and_capture_obligation
    (w : W (σ := σ)) {x : Var} {φ : Formula σ}
    (hTruthLt :
      ∀ ψ : Formula σ,
        Syntax.fSize (σ := σ) ψ < Syntax.fSize (σ := σ) (.sigma x φ) →
          (Forces (canonicalModel (σ := σ)) idVarValuation w ψ ↔ ψ ∈ w.carrier))
    (hSigmaForce :
      Forces (canonicalModel (σ := σ)) idVarValuation w (.sigma x φ)) :
    (.sigma x φ : Formula σ) ∈ w.carrier := by
  rcases hSigmaForce with ⟨d, hBody⟩
  have hSubstForce :
      Forces (canonicalModel (σ := σ)) idVarValuation w
        (Syntax.substFormula (σ := σ) x (.var d) φ) :=
    (KripkeFO.forces_substFormula_var
      (σ := σ)
      (M := canonicalModel (σ := σ))
      (ρ := idVarValuation)
      (w := w)
      x d φ).2 hBody
  have hSizeEq :
      Syntax.fSize (σ := σ) (Syntax.substFormula (σ := σ) x (.var d) φ) =
        Syntax.fSize (σ := σ) φ :=
    Syntax.fSize_substFormula_var (x := x) (a := d) φ
  have hSizeLt :
      Syntax.fSize (σ := σ) (Syntax.substFormula (σ := σ) x (.var d) φ) <
        Syntax.fSize (σ := σ) (.sigma x φ) := by
    simp [hSizeEq, Syntax.fSize]
  have hSubstMem :
      Syntax.substFormula (σ := σ) x (.var d) φ ∈ w.carrier :=
    (hTruthLt (Syntax.substFormula (σ := σ) x (.var d) φ) hSizeLt).1 hSubstForce
  have hDerSubst : Derivable (σ := σ) w.carrier
      (Syntax.substFormula (σ := σ) x (.var d) φ) :=
    derivable_of_mem (σ := σ) (T := w.carrier) hSubstMem
  have hDerSigma : Derivable (σ := σ) w.carrier (.sigma x φ) := by
    rcases hDerSubst with ⟨Γ, hΓ, hDerΓ⟩
    exact ⟨Γ, hΓ, Derives.sigmaI (x := x) (a := d) (φ := φ) hDerΓ⟩
  exact w.closed _ hDerSigma

/--
Quantifier truth-lemma helper (`pi`, membership -> forcing) for fresh instantiated values.

This is the quantifier-introduction direction used in the canonical truth development;
the fully general `∀ d` clause is deferred to the final internal completeness artifact.
-/
lemma canonical_forces_pi_of_mem_fresh
    (w : W (σ := σ)) {x d : Var} {φ : Formula σ}
    (hdVars : d ∉ Syntax.varsFormula (σ := σ) φ)
    (hSubst :
      Syntax.substFormula (σ := σ) x (.var d) φ ∈ w.carrier →
      Forces (canonicalModel (σ := σ)) idVarValuation w
        (Syntax.substFormula (σ := σ) x (.var d) φ))
    (hPi : (.pi x φ : Formula σ) ∈ w.carrier) :
    Forces (canonicalModel (σ := σ)) (update idVarValuation x d) w φ := by
  have hInstMem :
      Syntax.substFormula (σ := σ) x (.var d) φ ∈ w.carrier :=
    w.pi_instance_mem (x := x) (a := d) (φ := φ) hdVars hPi
  have hInstForces :
      Forces (canonicalModel (σ := σ)) idVarValuation w
        (Syntax.substFormula (σ := σ) x (.var d) φ) :=
    hSubst hInstMem
  have hBody :
      Forces (canonicalModel (σ := σ))
        (update idVarValuation x (idVarValuation d)) w φ :=
    (KripkeFO.forces_substFormula_var
      (σ := σ)
      (M := canonicalModel (σ := σ))
      (ρ := idVarValuation)
      (w := w)
      x d φ).1 hInstForces
  simpa [idVarValuation, update_self] using hBody

lemma canonical_forces_pi_of_mem_not_mem_boundVars
    (w : W (σ := σ)) {x d : Var} {φ : Formula σ}
    (hdBound : d ∉ Syntax.boundVars (σ := σ) φ)
    (hSubst :
      Syntax.substFormula (σ := σ) x (.var d) φ ∈ w.carrier →
      Forces (canonicalModel (σ := σ)) idVarValuation w
        (Syntax.substFormula (σ := σ) x (.var d) φ))
    (hPi : (.pi x φ : Formula σ) ∈ w.carrier) :
    Forces (canonicalModel (σ := σ)) (update idVarValuation x d) w φ := by
  have hInstMem :
      Syntax.substFormula (σ := σ) x (.var d) φ ∈ w.carrier :=
    w.pi_instance_mem_of_not_mem_boundVars (x := x) (a := d) (φ := φ) hdBound hPi
  have hInstForces :
      Forces (canonicalModel (σ := σ)) idVarValuation w
        (Syntax.substFormula (σ := σ) x (.var d) φ) :=
    hSubst hInstMem
  have hBody :
      Forces (canonicalModel (σ := σ))
        (update idVarValuation x (idVarValuation d)) w φ :=
    (KripkeFO.forces_substFormula_var
      (σ := σ)
      (M := canonicalModel (σ := σ))
      (ρ := idVarValuation)
      (w := w)
      x d φ).1 hInstForces
  simpa [idVarValuation, update_self] using hBody

/--
Quantifier truth helper (`pi`, membership -> forcing for a fixed witness) driven by a
smaller-formula truth oracle.

This is the size-recursive version of `canonical_forces_pi_of_mem_not_mem_boundVars`.
-/
lemma canonical_forces_pi_of_mem_not_mem_boundVars_of_lt
    (w : W (σ := σ)) {x d : Var} {φ : Formula σ}
    (hTruthLt :
      ∀ ψ : Formula σ,
        Syntax.fSize (σ := σ) ψ < Syntax.fSize (σ := σ) (.pi x φ) →
          (Forces (canonicalModel (σ := σ)) idVarValuation w ψ ↔ ψ ∈ w.carrier))
    (hdBound : d ∉ Syntax.boundVars (σ := σ) φ)
    (hPi : (.pi x φ : Formula σ) ∈ w.carrier) :
    Forces (canonicalModel (σ := σ)) (update idVarValuation x d) w φ := by
  refine canonical_forces_pi_of_mem_not_mem_boundVars
    (σ := σ) (w := w) (x := x) (d := d) (φ := φ) hdBound ?_ hPi
  intro hInstMem
  have hSizeEq :
      Syntax.fSize (σ := σ) (Syntax.substFormula (σ := σ) x (.var d) φ) =
        Syntax.fSize (σ := σ) φ :=
    Syntax.fSize_substFormula_var (x := x) (a := d) φ
  have hSizeLt :
      Syntax.fSize (σ := σ) (Syntax.substFormula (σ := σ) x (.var d) φ) <
        Syntax.fSize (σ := σ) (.pi x φ) := by
    simp [hSizeEq, Syntax.fSize]
  have hSubstTruthFun :
      Syntax.fSize (σ := σ) (Syntax.substFormula (σ := σ) x (.var d) φ) <
          Syntax.fSize (σ := σ) (.pi x φ) →
        (Forces (canonicalModel (σ := σ)) idVarValuation w
            (Syntax.substFormula (σ := σ) x (.var d) φ) ↔
          Syntax.substFormula (σ := σ) x (.var d) φ ∈ w.carrier) := by
    exact hTruthLt (Syntax.substFormula (σ := σ) x (.var d) φ)
  have hSubstTruth :
      Forces (canonicalModel (σ := σ)) idVarValuation w
          (Syntax.substFormula (σ := σ) x (.var d) φ) ↔
        Syntax.substFormula (σ := σ) x (.var d) φ ∈ w.carrier :=
    hSubstTruthFun hSizeLt
  exact hSubstTruth.2 hInstMem

/-- Canonical `pi` forward direction (membership -> forcing) via unrestricted `piE`. -/
lemma canonical_forces_pi_of_mem_of_lt_and_capture_obligation
    (w : W (σ := σ)) {x d : Var} {φ : Formula σ}
    (hTruthLt :
      ∀ ψ : Formula σ,
        Syntax.fSize (σ := σ) ψ < Syntax.fSize (σ := σ) (.pi x φ) →
          (Forces (canonicalModel (σ := σ)) idVarValuation w ψ ↔ ψ ∈ w.carrier))
    (hPi : (.pi x φ : Formula σ) ∈ w.carrier) :
    Forces (canonicalModel (σ := σ)) (update idVarValuation x d) w φ := by
  have hDerInst : Derivable (σ := σ) w.carrier
      (Syntax.substFormula (σ := σ) x (.var d) φ) := by
    refine derivable_of_derives (σ := σ) (T := w.carrier)
      (Γ := [.pi x φ]) (φ := Syntax.substFormula (σ := σ) x (.var d) φ) ?_ ?_
    · intro ψ hψ
      simp at hψ
      subst hψ
      exact hPi
    · exact Derives.piE (x := x) (a := d) (φ := φ) (Derives.hyp (by simp))
  have hSubstMem :
      Syntax.substFormula (σ := σ) x (.var d) φ ∈ w.carrier :=
    w.closed _ hDerInst
  have hSizeEq :
      Syntax.fSize (σ := σ) (Syntax.substFormula (σ := σ) x (.var d) φ) =
        Syntax.fSize (σ := σ) φ :=
    Syntax.fSize_substFormula_var (x := x) (a := d) φ
  have hSizeLt :
      Syntax.fSize (σ := σ) (Syntax.substFormula (σ := σ) x (.var d) φ) <
        Syntax.fSize (σ := σ) (.pi x φ) := by
    simp [hSizeEq, Syntax.fSize]
  have hSubstForce :
      Forces (canonicalModel (σ := σ)) idVarValuation w
        (Syntax.substFormula (σ := σ) x (.var d) φ) :=
    (hTruthLt (Syntax.substFormula (σ := σ) x (.var d) φ) hSizeLt).2 hSubstMem
  have hBody :
      Forces (canonicalModel (σ := σ))
        (update idVarValuation x (idVarValuation d)) w φ :=
    (KripkeFO.forces_substFormula_var
      (σ := σ)
      (M := canonicalModel (σ := σ))
      (ρ := idVarValuation)
      (w := w)
      x d φ).1 hSubstForce
  simpa [idVarValuation, update_self] using hBody

/--
Missing `pi` converse isolated as a single generalization obligation.

If every variable-instance of `pi` is already in `w.carrier`, `hPiGeneralize` provides the
final step to conclude `(.pi x φ) ∈ w.carrier`.
-/
class HasCanonicalPiGeneralization : Prop where
  pi_generalize :
    ∀ (w : W (σ := σ)) (x : Var) (φ : Formula σ),
      (∀ a : Var, Syntax.substFormula (σ := σ) x (.var a) φ ∈ w.carrier) →
      (.pi x φ : Formula σ) ∈ w.carrier

/--
Optional global closed-theory hypothesis for canonical worlds.

This is useful for the sentence-family closure route where maximal members are known closed.
-/
class HasCanonicalTheoryClosed : Prop where
  closed_mem :
    ∀ {w : W (σ := σ)} {ψ : Formula σ},
      ψ ∈ w.carrier →
      Syntax.fvFormula (σ := σ) ψ = ∅

instance (priority := 96)
    hasCanonicalPiGeneralization_of_theoryClosed
    [HasCanonicalTheoryClosed (σ := σ)] :
    HasCanonicalPiGeneralization (σ := σ) where
  pi_generalize := by
    intro w x φ hAllInst
    let θ : Formula σ := Syntax.substFormula (σ := σ) x (.var (ND.freshSigmaEigen (σ := σ) [] φ (.top : Formula σ))) φ
    let a : Var := ND.freshSigmaEigen (σ := σ) [] φ (.top : Formula σ)
    have haVars : a ∉ Syntax.varsFormula (σ := σ) φ :=
      ND.freshSigmaEigen_not_mem_varsFormula (σ := σ) [] φ (.top : Formula σ)
    have hθMem : θ ∈ w.carrier := by
      simpa [θ, a] using hAllInst a
    have hθClosed : Syntax.fvFormula (σ := σ) θ = ∅ :=
      HasCanonicalTheoryClosed.closed_mem (σ := σ) (w := w) (ψ := θ) hθMem
    have haCtx : a ∉ ND.fvContext (σ := σ) [θ] := by
      simp [ND.fvContext, hθClosed, a]
    have hDerθ : Derives (σ := σ) [θ] θ := Derives.hyp (by simp [θ])
    have hDerPi : Derives (σ := σ) [θ] (.pi x φ) :=
      Derives.piI (x := x) (a := a) (φ := φ) haCtx haVars hDerθ
    have hDerivablePi : Derivable (σ := σ) w.carrier (.pi x φ) := by
      refine ⟨[θ], ?_, hDerPi⟩
      intro ψ hψ
      simpa [θ] using (show ψ = θ from by simpa using hψ) ▸ hθMem
    exact w.closed _ hDerivablePi

/--
Canonical `pi` converse (forcing -> membership), reduced to:
- smaller-formula truth for instantiated bodies, and
- one explicit `pi`-generalization obligation.
-/
lemma canonical_pi_mem_of_forces_of_lt_and_generalization
    (w : W (σ := σ)) {x : Var} {φ : Formula σ}
    (hTruthLt :
      ∀ ψ : Formula σ,
        Syntax.fSize (σ := σ) ψ < Syntax.fSize (σ := σ) (.pi x φ) →
          (Forces (canonicalModel (σ := σ)) idVarValuation w ψ ↔ ψ ∈ w.carrier))
    (hPiGeneralize :
      (∀ a : Var, Syntax.substFormula (σ := σ) x (.var a) φ ∈ w.carrier) →
      (.pi x φ : Formula σ) ∈ w.carrier)
    (hPiForce :
      Forces (canonicalModel (σ := σ)) idVarValuation w (.pi x φ)) :
    (.pi x φ : Formula σ) ∈ w.carrier := by
  apply hPiGeneralize
  intro a
  have hBody :
      Forces (canonicalModel (σ := σ))
        (update idVarValuation x (idVarValuation a)) w φ :=
    hPiForce w (by rfl) a
  have hSubstForce :
      Forces (canonicalModel (σ := σ)) idVarValuation w
        (Syntax.substFormula (σ := σ) x (.var a) φ) :=
    (KripkeFO.forces_substFormula_var
      (σ := σ)
      (M := canonicalModel (σ := σ))
      (ρ := idVarValuation)
      (w := w)
      x a φ).2 hBody
  have hSizeEq :
      Syntax.fSize (σ := σ) (Syntax.substFormula (σ := σ) x (.var a) φ) =
        Syntax.fSize (σ := σ) φ :=
    Syntax.fSize_substFormula_var (x := x) (a := a) φ
  have hSizeLt :
      Syntax.fSize (σ := σ) (Syntax.substFormula (σ := σ) x (.var a) φ) <
        Syntax.fSize (σ := σ) (.pi x φ) := by
    simp [hSizeEq, Syntax.fSize]
  exact (hTruthLt (Syntax.substFormula (σ := σ) x (.var a) φ) hSizeLt).1 hSubstForce

/--
Canonical `sigma` truth from smaller-formula truth.

This packages both directions (`membership -> forcing` and `forcing -> membership`) into one
reusable step for size-recursive truth-lemma construction.
-/
lemma canonical_sigma_forces_iff_mem_of_lt
    (w : W (σ := σ)) {x : Var} {φ : Formula σ}
    (hTruthLt :
      ∀ ψ : Formula σ,
        Syntax.fSize (σ := σ) ψ < Syntax.fSize (σ := σ) (.sigma x φ) →
          (Forces (canonicalModel (σ := σ)) idVarValuation w ψ ↔ ψ ∈ w.carrier)) :
    Forces (canonicalModel (σ := σ)) idVarValuation w (.sigma x φ) ↔
      (.sigma x φ : Formula σ) ∈ w.carrier := by
  constructor
  · intro hForce
    exact canonical_sigma_mem_of_forces_of_lt_and_capture_obligation
      (σ := σ) (w := w) (x := x) (φ := φ) hTruthLt hForce
  · intro hSigma
    exact canonical_forces_sigma_of_mem_of_lt
      (σ := σ) (w := w) (x := x) (φ := φ) hTruthLt hSigma

/--
Canonical `pi` truth at `w` from:
- smaller-formula truth on all extensions `v ≥ w`, and
- extension-stable `pi`-generalization.

This is the valid `pi` analogue of `canonical_sigma_forces_iff_mem_of_lt` for the
Kripke-monotone setting where forcing of `pi` quantifies over all `v ≥ w`.
-/
lemma canonical_pi_forces_iff_mem_of_lt_and_generalization_on_extensions
    (w : W (σ := σ)) {x : Var} {φ : Formula σ}
    (hTruthLt :
      ∀ v : W (σ := σ), w ≤ v →
        ∀ ψ : Formula σ,
          Syntax.fSize (σ := σ) ψ < Syntax.fSize (σ := σ) (.pi x φ) →
            (Forces (canonicalModel (σ := σ)) idVarValuation v ψ ↔ ψ ∈ v.carrier))
    (hPiGeneralize :
      ∀ v : W (σ := σ), w ≤ v →
        (∀ a : Var, Syntax.substFormula (σ := σ) x (.var a) φ ∈ v.carrier) →
        (.pi x φ : Formula σ) ∈ v.carrier) :
    Forces (canonicalModel (σ := σ)) idVarValuation w (.pi x φ) ↔
      (.pi x φ : Formula σ) ∈ w.carrier := by
  constructor
  · intro hForce
    exact canonical_pi_mem_of_forces_of_lt_and_generalization
      (σ := σ)
      (w := w) (x := x) (φ := φ)
      (hTruthLt := hTruthLt w (by rfl))
      (hPiGeneralize := hPiGeneralize w (by rfl))
      hForce
  · intro hPiMem v hwv a
    have hPiMemV : (.pi x φ : Formula σ) ∈ v.carrier := hwv hPiMem
    exact canonical_forces_pi_of_mem_of_lt_and_capture_obligation
      (σ := σ)
      (w := v) (x := x) (d := a) (φ := φ)
      (hTruthLt := hTruthLt v hwv)
      hPiMemV

/--
Theory-closed specialization of
`canonical_pi_forces_iff_mem_of_lt_and_generalization_on_extensions`.
-/
lemma canonical_pi_forces_iff_mem_of_lt_on_extensions_of_theoryClosed
    [HasCanonicalTheoryClosed (σ := σ)]
    (w : W (σ := σ)) {x : Var} {φ : Formula σ}
    (hTruthLt :
      ∀ v : W (σ := σ), w ≤ v →
        ∀ ψ : Formula σ,
          Syntax.fSize (σ := σ) ψ < Syntax.fSize (σ := σ) (.pi x φ) →
            (Forces (canonicalModel (σ := σ)) idVarValuation v ψ ↔ ψ ∈ v.carrier)) :
    Forces (canonicalModel (σ := σ)) idVarValuation w (.pi x φ) ↔
      (.pi x φ : Formula σ) ∈ w.carrier := by
  exact canonical_pi_forces_iff_mem_of_lt_and_generalization_on_extensions
    (σ := σ)
    (w := w) (x := x) (φ := φ)
    (hTruthLt := hTruthLt)
    (hPiGeneralize := by
      intro v hwv hAllInst
      exact HasCanonicalPiGeneralization.pi_generalize (σ := σ) v x φ hAllInst)

/--
If we can build an internal canonical countermodel for every non-derivable sequent,
semantic entailment implies derivability.

This isolates the remaining FO completeness work to one concrete internal artifact:
countermodel construction in the `InternalFO` canonical shell.
-/
theorem completeness_from_countermodel
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hCounter :
      ¬ Derives (σ := σ) Γ φ →
        ∃ w : W (σ := σ),
          (∀ ψ ∈ Γ, Forces (canonicalModel (σ := σ)) idVarValuation w ψ) ∧
          ¬ Forces (canonicalModel (σ := σ)) idVarValuation w φ) :
    Entails (σ := σ) Γ φ → Derives (σ := σ) Γ φ := by
  intro hEnt
  by_contra hNotDer
  rcases hCounter hNotDer with ⟨w, hwΓ, hNotForce⟩
  have hForce : Forces (canonicalModel (σ := σ)) idVarValuation w φ :=
    hEnt (W := W (σ := σ))
      (D := Var)
      (M := canonicalModel (σ := σ))
      (ρ := idVarValuation)
      (w := w)
      hwΓ
  exact hNotForce hForce

/--
Build the canonical countermodel artifact from two concrete internal ingredients:
1) world-extension construction avoiding an underivable goal;
2) canonical truth lemma (`Forces` iff membership).
-/
theorem countermodel_of_extension_and_truth
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hExtend :
      ¬ Derives (σ := σ) Γ φ →
        ∃ w : W (σ := σ),
          (∀ ψ ∈ Γ, ψ ∈ w.carrier) ∧
          φ ∉ w.carrier)
    (hTruth :
      ∀ (w : W (σ := σ)) (ψ : Formula σ),
        Forces (canonicalModel (σ := σ)) idVarValuation w ψ ↔ ψ ∈ w.carrier) :
    ¬ Derives (σ := σ) Γ φ →
      ∃ w : W (σ := σ),
        (∀ ψ ∈ Γ, Forces (canonicalModel (σ := σ)) idVarValuation w ψ) ∧
        ¬ Forces (canonicalModel (σ := σ)) idVarValuation w φ := by
  intro hNotDer
  rcases hExtend hNotDer with ⟨w, hΓmem, hNotMem⟩
  refine ⟨w, ?_, ?_⟩
  · intro ψ hψ
    exact (hTruth w ψ).2 (hΓmem ψ hψ)
  · intro hForce
    exact hNotMem ((hTruth w φ).1 hForce)

/-- Internal obligation A: construct a saturated world extending assumptions while avoiding a goal. -/
class HasExtensionConstruction : Prop where
  extend_avoid :
    ∀ {Γ : List (Formula σ)} {φ : Formula σ},
      ¬ Derives (σ := σ) Γ φ →
        ∃ w : W (σ := σ),
          (∀ ψ ∈ Γ, ψ ∈ w.carrier) ∧
          φ ∉ w.carrier

/--
Bridge obligation from list sequents to the set-based Lindenbaum family base facts.

This isolates the remaining gap caused by eigenvariable-sensitive weakening in `Derives`.
-/
class HasSequentFamilyBase : Prop where
  base_consistent :
    ∀ {Γ : List (Formula σ)} {φ : Formula σ},
      ¬ Derives (σ := σ) Γ φ →
        Consistent (σ := σ) (fun ψ => ψ ∈ Γ)
  base_notDerivable :
    ∀ {Γ : List (Formula σ)} {φ : Formula σ},
      ¬ Derives (σ := σ) Γ φ →
        ¬ Derivable (σ := σ) (fun ψ => ψ ∈ Γ) φ

/--
Structural metatheory obligation: unrestricted list-context weakening for `Derives`.

This is the exact proof-theoretic property needed to discharge `HasSequentFamilyBase`
without routing through semantic completeness.
-/
class HasOpenWeakening : Prop where
  weaken :
    ∀ {Γ Δ : List (Formula σ)} {φ : Formula σ},
      Derives (σ := σ) Γ φ →
      Γ ⊆ Δ →
      Derives (σ := σ) Δ φ

instance (priority := 100)
    hasOpenWeakening_of_nd
    : HasOpenWeakening (σ := σ) where
  weaken := by
    intro Γ Δ φ hDer hSub
    exact Derives.wk hDer hSub

instance (priority := 95)
    hasSequentFamilyBase_of_openWeakening
    [HasOpenWeakening (σ := σ)] :
    HasSequentFamilyBase (σ := σ) where
  base_consistent := by
    intro Γ φ hNotDer hInconsistent
    rcases hInconsistent with ⟨Δ, hΔS, hDerBot⟩
    have hSub : Δ ⊆ Γ := by
      intro ψ hψ
      exact hΔS ψ hψ
    have hDerBotΓ : Derives (σ := σ) Γ (.bot : Formula σ) :=
      HasOpenWeakening.weaken (σ := σ) hDerBot hSub
    exact hNotDer (Derives.botE hDerBotΓ)
  base_notDerivable := by
    intro Γ φ hNotDer hDerivable
    rcases hDerivable with ⟨Δ, hΔS, hDerΔ⟩
    have hSub : Δ ⊆ Γ := by
      intro ψ hψ
      exact hΔS ψ hψ
    have hDerΓ : Derives (σ := σ) Γ φ :=
      HasOpenWeakening.weaken (σ := σ) hDerΔ hSub
    exact hNotDer hDerΓ

/--
Monotonicity of semantic entailment under context inclusion.

If every assumption in `Δ` appears in `Γ`, then any entailment from `Δ` also holds from `Γ`.
-/
lemma entails_mono_of_subset
    {Γ Δ : List (Formula σ)} {φ : Formula σ}
    (hSub : Δ ⊆ Γ) :
    Entails (σ := σ) Δ φ → Entails (σ := σ) Γ φ := by
  intro hEnt W _ D M ρ w hΓ
  apply hEnt W D M ρ w
  intro ψ hψ
  exact hΓ ψ (hSub hψ)

/--
Promotion obligation: convert a maximal Lindenbaum family member into a saturated canonical world.
-/
class HasSaturatedPromotion : Prop where
  of_maximal :
    ∀ {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)},
      M ∈ Lindenbaum.Family (σ := σ) S χ →
      Maximal (· ∈ Lindenbaum.Family (σ := σ) S χ) M →
      ∃ w : W (σ := σ), S ⊆ w.carrier ∧ χ ∉ w.carrier

/--
Focused remaining FO promotion obligation:
construct Henkin witnesses for `sigma` formulas in maximal Lindenbaum members.

This isolates the truly quantifier-specific part from the generic maximality/closure/prime layer.
-/
class HasHenkinSigmaPromotion : Prop where
  sigma_witness_of_maximal :
    ∀ {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)},
      M ∈ Lindenbaum.Family (σ := σ) S χ →
      Maximal (· ∈ Lindenbaum.Family (σ := σ) S χ) M →
      ∀ {x : Var} {φ : Formula σ},
        (.sigma x φ : Formula σ) ∈ M →
          ∃ a : Var,
            a ∉ Syntax.varsFormula (σ := σ) φ ∧
            Syntax.substFormula (σ := σ) x (.var a) φ ∈ M

/--
Focused insertion obligation for sigma-Henkinization at maximal Lindenbaum members.

This isolates the remaining quantifier blocker to one concrete step: find a fresh witness
whose body-instance can be inserted while staying inside the same family.
-/
class HasWitnessInsertionFamily : Prop where
  insert_sigma_witness_family :
    ∀ {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)},
      M ∈ Lindenbaum.Family (σ := σ) S χ →
      Maximal (· ∈ Lindenbaum.Family (σ := σ) S χ) M →
      ∀ {x : Var} {φ : Formula σ},
        (.sigma x φ : Formula σ) ∈ M →
          ∃ a : Var,
            a ∉ Syntax.varsFormula (σ := σ) φ ∧
            Set.insert (Syntax.substFormula (σ := σ) x (.var a) φ) M ∈
              Lindenbaum.Family (σ := σ) S χ

/--
Open-context obstruction witness for B1-style freshness extraction.

Even with `a ∉ fvFormula χ`, a derivation from an inserted witness instance can legitimately rely on
an assumption that still mentions `a` in the context tail. This shows why post-hoc tail-fresh
extraction cannot be expected from structural decomposition alone.
-/
lemma derives_insert_witness_dep_example
    {x a : Var} {φ χ : Formula σ} :
    Derives (σ := σ)
      (Syntax.substFormula (σ := σ) x (.var a) φ ::
        [.imp (Syntax.substFormula (σ := σ) x (.var a) φ) χ]) χ := by
  let θ : Formula σ := Syntax.substFormula (σ := σ) x (.var a) φ
  have hImp : Derives (σ := σ) [θ, .imp θ χ] (.imp θ χ) :=
    Derives.hyp (by simp)
  have hθ : Derives (σ := σ) [θ, .imp θ χ] θ :=
    Derives.hyp (by simp)
  simpa [θ] using Derives.impE hImp hθ

/--
In the obstruction witness above, the tail context can contain formulas that mention the witness
variable `a`.
-/
lemma witness_dep_example_tail_mentions_witness
    {x a : Var} {φ χ : Formula σ}
    (ha : a ∈ Syntax.fvFormula (σ := σ) (Syntax.substFormula (σ := σ) x (.var a) φ)) :
    a ∈ ND.fvContext (σ := σ)
      ([.imp (Syntax.substFormula (σ := σ) x (.var a) φ) χ] : List (Formula σ)) := by
  have haImp :
      a ∈ Syntax.fvFormula (σ := σ)
        (.imp (Syntax.substFormula (σ := σ) x (.var a) φ) χ) := by
    simp [Syntax.fvFormula, Finset.mem_union, ha]
  exact (ND.mem_fvContext_iff (σ := σ)
      (x := a)
      (Γ := ([.imp (Syntax.substFormula (σ := σ) x (.var a) φ) χ] : List (Formula σ)))).2
    ⟨.imp (Syntax.substFormula (σ := σ) x (.var a) φ) χ, by simp, haImp⟩

/--
No unrestricted source-fresh extractor can hold in the open-formula setting.

If the theory can mention the inserted witness variable in the tail context, there exists a
derivation shape where `a` necessarily appears in `fvContext`.
-/
lemma no_unrestricted_source_fresh_extractor_of_tail_mention
    {T : Set (Formula σ)} {x a : Var} {φ χ : Formula σ}
    (hImpMem : (.imp (Syntax.substFormula (σ := σ) x (.var a) φ) χ : Formula σ) ∈ T)
    (ha : a ∈ Syntax.fvFormula (σ := σ) (Syntax.substFormula (σ := σ) x (.var a) φ)) :
    ¬ (∀ Γ : List (Formula σ),
          (∀ ψ ∈ Γ, ψ ∈ T) →
          Derives (σ := σ) (Syntax.substFormula (σ := σ) x (.var a) φ :: Γ) χ →
          a ∉ ND.fvContext (σ := σ) Γ) := by
  intro hSourceFresh
  let Γ0 : List (Formula σ) := [.imp (Syntax.substFormula (σ := σ) x (.var a) φ) χ]
  have hΓ0T : ∀ ψ ∈ Γ0, ψ ∈ T := by
    intro ψ hψ
    have hψEq : ψ = (.imp (Syntax.substFormula (σ := σ) x (.var a) φ) χ : Formula σ) := by
      simpa [Γ0] using hψ
    simpa [hψEq] using hImpMem
  have hDer : Derives (σ := σ) (Syntax.substFormula (σ := σ) x (.var a) φ :: Γ0) χ := by
    simpa [Γ0] using
      (derives_insert_witness_dep_example (σ := σ) (x := x) (a := a) (φ := φ) (χ := χ))
  have hFresh : a ∉ ND.fvContext (σ := σ) Γ0 :=
    hSourceFresh Γ0 hΓ0T hDer
  have hMention : a ∈ ND.fvContext (σ := σ) Γ0 := by
    simpa [Γ0] using
      (witness_dep_example_tail_mentions_witness
        (σ := σ) (x := x) (a := a) (φ := φ) (χ := χ) ha)
  exact hFresh hMention

/--
Final focused quantifier blocker:
from derivability over an inserted witness-instance, extract a derivation in a context where
the witness variable is fresh for the context and conclusion.

This is stated on the exact Lindenbaum slice used by the canonical construction
(family membership + maximality). The unrestricted version over arbitrary `M`
is not sound in this open-formula ND setting.
-/
class HasFreshSigmaConsFromInsertOnFamily : Prop where
  fresh_cons_of_derivable_insert :
    ∀ {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)}
      {x a : Var} {φ : Formula σ},
      M ∈ Lindenbaum.Family (σ := σ) S χ →
      Maximal (· ∈ Lindenbaum.Family (σ := σ) S χ) M →
      a ∉ Syntax.varsFormula (σ := σ) φ →
      a ∉ Syntax.fvFormula (σ := σ) χ →
      Derivable (σ := σ) (Set.insert (Syntax.substFormula (σ := σ) x (.var a) φ) M) χ →
        ∃ b : Var, ∃ Γ : List (Formula σ),
          b ∉ ND.fvContext (σ := σ) Γ ∧
          b ∉ Syntax.varsFormula (σ := σ) φ ∧
          b ∉ Syntax.fvFormula (σ := σ) χ ∧
          (∀ ψ ∈ Γ, ψ ∈ M) ∧
          Derives (σ := σ) (Syntax.substFormula (σ := σ) x (.var b) φ :: Γ) χ

/--
Focused tail-fresh extraction obligation for inserted sigma witnesses.

Compared to `HasFreshSigmaConsFromInsertOnFamily`, this keeps the witness variable fixed and asks
for a derivation shape where freshness is only required on the *tail* context extracted from `M`.
The witness-renaming step to a canonical fresh eigenvariable is handled separately.
-/
class HasTailFreshSigmaConsOnFamily : Prop where
  tail_fresh_cons_of_derivable_insert :
    ∀ {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)}
      {x a : Var} {φ : Formula σ},
      M ∈ Lindenbaum.Family (σ := σ) S χ →
      Maximal (· ∈ Lindenbaum.Family (σ := σ) S χ) M →
      a ∉ Syntax.varsFormula (σ := σ) φ →
      a ∉ Syntax.fvFormula (σ := σ) χ →
      Derivable (σ := σ) (Set.insert (Syntax.substFormula (σ := σ) x (.var a) φ) M) χ →
        ∃ Γ : List (Formula σ),
          a ∉ ND.fvContext (σ := σ) Γ ∧
          (∀ ψ ∈ Γ, ψ ∈ M) ∧
          Derives (σ := σ) (Syntax.substFormula (σ := σ) x (.var a) φ :: Γ) χ

/--
Stronger extraction interface: derive the inserted-witness implication in the freshness-tracked
quantifier calculus (`DerivesEFresh`).

Compared to direct cons-context extraction, this avoids requiring freshness on
`(subst x b φ :: Γ)` itself. We only track freshness on `Γ`, then recover the cons-shape by one
`impE` step.
-/
class HasFreshDerivesEFreshImpOnFamily : Prop where
  fresh_derivesE_imp_of_derivable_insert :
    ∀ {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)}
      {x a : Var} {φ : Formula σ},
      M ∈ Lindenbaum.Family (σ := σ) S χ →
      Maximal (· ∈ Lindenbaum.Family (σ := σ) S χ) M →
      a ∉ Syntax.varsFormula (σ := σ) φ →
      a ∉ Syntax.fvFormula (σ := σ) χ →
      Derivable (σ := σ) (Set.insert (Syntax.substFormula (σ := σ) x (.var a) φ) M) χ →
        ∃ b : Var, ∃ Γ : List (Formula σ),
          b ∉ Syntax.varsFormula (σ := σ) φ ∧
          b ∉ Syntax.fvFormula (σ := σ) χ ∧
          (∀ ψ ∈ Γ, ψ ∈ M) ∧
          ND.DerivesEFresh (σ := σ) b
            Γ
            (.imp (Syntax.substFormula (σ := σ) x (.var b) φ) χ)

/--
Build the `DerivesEFresh` implication extraction interface directly from a fresh-cons extractor.

This is a structural bridge:
- `fresh_cons` gives a derivation of `χ` from `(subst x b φ :: Γ)`,
- then `impI` discharges the head assumption,
- and `DerivesEFresh.ofDerives` tracks `b ∉ fvContext Γ`.
-/
theorem hasFreshDerivesEFreshImpOnFamily_of_freshCons
    [HasFreshSigmaConsFromInsertOnFamily (σ := σ)] :
    HasFreshDerivesEFreshImpOnFamily (σ := σ) := by
  refine ⟨?_⟩
  intro S χ M x a φ hMF hMax haVars haχ hDerIns
  rcases HasFreshSigmaConsFromInsertOnFamily.fresh_cons_of_derivable_insert
    (σ := σ) (S := S) (χ := χ) (M := M) (x := x) (a := a) (φ := φ)
    hMF hMax haVars haχ hDerIns with
    ⟨b, Γ, hbΓ, hbVars, hbχ, hΓM, hDerCons⟩
  let θb : Formula σ := Syntax.substFormula (σ := σ) x (.var b) φ
  have hDerImp : Derives (σ := σ) Γ (.imp θb χ) := Derives.impI hDerCons
  refine ⟨b, Γ, hbVars, hbχ, hΓM, ?_⟩
  simpa [θb] using ND.DerivesEFresh.ofDerives (σ := σ) hbΓ hDerImp

/--
Recover the standard fresh-cons family obligation from a `DerivesEFresh` extraction artifact.
-/
theorem hasFreshSigmaConsFromInsertOnFamily_of_derivesEFreshImp
    [HasFreshDerivesEFreshImpOnFamily (σ := σ)] :
    HasFreshSigmaConsFromInsertOnFamily (σ := σ) := by
  refine ⟨?_⟩
  intro S χ M x a φ hMF hMax haVars haχ hχIns
  rcases HasFreshDerivesEFreshImpOnFamily.fresh_derivesE_imp_of_derivable_insert
    (σ := σ) (S := S) (χ := χ) (M := M) (x := x) (a := a) (φ := φ)
    hMF hMax haVars haχ hχIns with
    ⟨b, Γ, hbVars, hbχ, hΓM, hDerFreshImp⟩
  let θb : Formula σ := Syntax.substFormula (σ := σ) x (.var b) φ
  have hbΓ : b ∉ ND.fvContext (σ := σ) Γ :=
    ND.DerivesEFresh.fresh_context (σ := σ) hDerFreshImp
  have hImp : Derives (σ := σ) Γ (.imp θb χ) :=
    ND.DerivesEFresh.toDerives (σ := σ) hDerFreshImp
  have hSub : Γ ⊆ (θb :: Γ) := by
    intro ψ hψ
    exact by simp [hψ]
  have hImpCons : Derives (σ := σ) (θb :: Γ) (.imp θb χ) :=
    Derives.wk hImp hSub
  have hHyp : Derives (σ := σ) (θb :: Γ) θb :=
    Derives.hyp (by simp [θb])
  have hCons : Derives (σ := σ) (θb :: Γ) χ :=
    Derives.impE hImpCons hHyp
  exact ⟨b, Γ, hbΓ, hbVars, hbχ, hΓM, by simpa [θb] using hCons⟩

instance (priority := 94)
    hasFreshSigmaConsFromInsertOnFamily_of_derivesEFreshImp_inst
    [HasFreshDerivesEFreshImpOnFamily (σ := σ)] :
    HasFreshSigmaConsFromInsertOnFamily (σ := σ) := by
  exact hasFreshSigmaConsFromInsertOnFamily_of_derivesEFreshImp (σ := σ)

-- This route is intentionally not used by default typeclass search.
attribute [-instance] hasFreshSigmaConsFromInsertOnFamily_of_derivesEFreshImp_inst

/--
The two focused B1 interfaces are equivalent:

- cons-context extraction (`HasFreshSigmaConsFromInsertOnFamily`), and
- implication extraction with freshness tracking (`HasFreshDerivesEFreshImpOnFamily`).
-/
theorem hasFreshSigmaConsFromInsertOnFamily_iff_hasFreshDerivesEFreshImpOnFamily :
    HasFreshSigmaConsFromInsertOnFamily (σ := σ) ↔
      HasFreshDerivesEFreshImpOnFamily (σ := σ) := by
  constructor
  · intro hFreshCons
    letI : HasFreshSigmaConsFromInsertOnFamily (σ := σ) := hFreshCons
    exact hasFreshDerivesEFreshImpOnFamily_of_freshCons (σ := σ)
  · intro hFreshImp
    letI : HasFreshDerivesEFreshImpOnFamily (σ := σ) := hFreshImp
    exact hasFreshSigmaConsFromInsertOnFamily_of_derivesEFreshImp (σ := σ)

/--
The `DerivesEFresh` implication extraction interface is inconsistent in the open-context ND setting.

Witness pattern:
- base theory contains `sigma x φ` and `imp (subst x a φ) χ`,
- `χ` is chosen false in a one-world model while `sigma x φ` and the implication are true,
- maximal extension gives `M ∈ Family S χ`,
- extraction would force a derivation of `χ` from `M`, contradicting `M ∈ Family S χ`.

No inhabited predicate signature is needed: the witness uses only `eExists` atoms.
-/
theorem not_hasFreshDerivesEFreshImpOnFamily :
    ¬ HasFreshDerivesEFreshImpOnFamily (σ := σ) := by
  classical
  intro hFresh
  letI : HasFreshDerivesEFreshImpOnFamily (σ := σ) := hFresh
  let x : Var := 1
  let a : Var := 0
  let c : Var := 2
  let φ : Formula σ := (.eExists (.var x) : Formula σ)
  let θa : Formula σ := Syntax.substFormula (σ := σ) x (.var a) φ
  let χ : Formula σ := (.eExists (.var c) : Formula σ)
  let sigmaφ : Formula σ := (.sigma x φ : Formula σ)
  let impθaχ : Formula σ := (.imp θa χ : Formula σ)
  let S : Set (Formula σ) := fun ψ => ψ = sigmaφ ∨ ψ = impθaχ
  have haVars : a ∉ Syntax.varsFormula (σ := σ) φ := by
    simp [a, x, φ, Syntax.varsFormula, Syntax.fvTerm]
  have haχ : a ∉ Syntax.fvFormula (σ := σ) χ := by
    simp [a, c, χ, Syntax.fvFormula, Syntax.fvTerm]
  let M0 : Model PUnit σ Var := {
    valPred := fun _ _ _ => True
    monoPred := by
      intro _ _ _ _ _ _
      trivial
    valEx := fun _ d => d = 1
    monoEx := by
      intro _ _ _ _ h
      exact h
  }
  let ρ : Valuation Var := fun v => v
  have hθaEq : θa = (.eExists (.var a) : Formula σ) := by
    have hNoAlpha :
        θa = Syntax.substFormulaVarNoAlpha (σ := σ) x a φ := by
      simpa [θa] using
        (Syntax.substFormula_var_eq_noAlpha_of_not_mem_varsFormula
          (σ := σ) x a φ haVars)
    calc
      θa = Syntax.substFormulaVarNoAlpha (σ := σ) x a φ := hNoAlpha
      _ = (.eExists (.var a) : Formula σ) := by
            simp [Syntax.substFormulaVarNoAlpha, Syntax.substTerm, φ, x, a]
  have hSigmaForce :
      Forces M0 ρ PUnit.unit sigmaφ := by
    refine ⟨1, ?_⟩
    simp [φ, M0, x, Forces, evalTerm, update]
  have hThetaFalse :
      ¬ Forces M0 ρ PUnit.unit θa := by
    rw [hθaEq]
    simp [M0, Forces, evalTerm, ρ, a]
  have hImpForce :
      Forces M0 ρ PUnit.unit impθaχ := by
    intro v _ hSub
    cases v
    exact (hThetaFalse (by simpa using hSub)).elim
  have hChiFalse :
      ¬ Forces M0 ρ PUnit.unit χ := by
    simp [χ, c, M0, Forces, evalTerm, ρ]
  have hSigmaMemS : sigmaφ ∈ S := by
    exact Or.inl rfl
  have hImpMemS : impθaχ ∈ S := by
    exact Or.inr rfl
  have hSForce :
      ∀ ψ, ψ ∈ S → Forces M0 ρ PUnit.unit ψ := by
    intro ψ hψ
    have hψCases : ψ = sigmaφ ∨ ψ = impθaχ := by
      simpa [S] using hψ
    rcases hψCases with rfl | rfl
    · exact hSigmaForce
    · exact hImpForce
  have hNoDerChi : ¬ Derivable (σ := σ) S χ := by
    intro hDerChi
    rcases hDerChi with ⟨Γ, hΓS, hDerΓChi⟩
    have hCtx :
        ∀ θ ∈ Γ, Forces M0 ρ PUnit.unit θ := by
      intro θ hθ
      exact hSForce θ (hΓS θ hθ)
    have hChiForce :
        Forces M0 ρ PUnit.unit χ :=
      KripkeFO.soundness (σ := σ) hDerΓChi
        (W := PUnit) (D := Var) (M := M0) (ρ := ρ) (w := PUnit.unit) hCtx
    exact hChiFalse hChiForce
  have hNoDerBot : ¬ Derivable (σ := σ) S (.bot : Formula σ) := by
    intro hDerBot
    rcases hDerBot with ⟨Γ, hΓS, hDerΓBot⟩
    have hCtx :
        ∀ θ ∈ Γ, Forces M0 ρ PUnit.unit θ := by
      intro θ hθ
      exact hSForce θ (hΓS θ hθ)
    have hBotForce :
        Forces M0 ρ PUnit.unit (.bot : Formula σ) :=
      KripkeFO.soundness (σ := σ) hDerΓBot
        (W := PUnit) (D := Var) (M := M0) (ρ := ρ) (w := PUnit.unit) hCtx
    exact hBotForce
  have hSCons : Consistent (σ := σ) S := hNoDerBot
  rcases Lindenbaum.exists_maximal (σ := σ) (S := S) (χ := χ) hSCons hNoDerChi with
    ⟨M, hSM, hMax⟩
  have hMF : M ∈ Lindenbaum.Family (σ := σ) S χ := hMax.prop
  have hImpMemM : impθaχ ∈ M := hSM hImpMemS
  have hSigmaMemM : sigmaφ ∈ M := hSM hSigmaMemS
  have hDerIns : Derivable (σ := σ) (Set.insert θa M) χ := by
    let Δ : List (Formula σ) := [.imp θa χ, θa]
    refine ⟨Δ, ?_, ?_⟩
    · intro ψ hψ
      have hCases : ψ = (.imp θa χ : Formula σ) ∨ ψ = θa := by
        simpa [Δ] using hψ
      rcases hCases with rfl | rfl
      · exact Or.inr hImpMemM
      · exact Or.inl rfl
    ·
      have hImp : Derives (σ := σ) Δ (.imp θa χ) := by
        simpa [Δ] using (Derives.hyp (σ := σ) (by simp))
      have hTheta : Derives (σ := σ) Δ θa := by
        simpa [Δ] using (Derives.hyp (σ := σ) (by simp))
      exact Derives.impE hImp hTheta
  rcases HasFreshDerivesEFreshImpOnFamily.fresh_derivesE_imp_of_derivable_insert
    (σ := σ) (S := S) (χ := χ) (M := M) (x := x) (a := a) (φ := φ)
    hMF hMax haVars haχ hDerIns with
    ⟨b, Γ, hbVars, hbχ, hΓM, hDerFreshImp⟩
  let θb : Formula σ := Syntax.substFormula (σ := σ) x (.var b) φ
  have hbΓ : b ∉ ND.fvContext (σ := σ) Γ :=
    ND.DerivesEFresh.fresh_context (σ := σ) hDerFreshImp
  have hImpDer : Derives (σ := σ) Γ (.imp θb χ) :=
    ND.DerivesEFresh.toDerives (σ := σ) hDerFreshImp
  have hbFvφ : b ∉ Syntax.fvFormula (σ := σ) φ :=
    Syntax.not_mem_fvFormula_of_not_mem_varsFormula (σ := σ) (a := b) (φ := φ) hbVars
  have hbSigma : b ∉ Syntax.fvFormula (σ := σ) sigmaφ := by
    intro hb
    have hbErase : b ∈ (Syntax.fvFormula (σ := σ) φ).erase x := by
      simpa [sigmaφ, Syntax.fvFormula] using hb
    exact hbFvφ (Finset.mem_erase.1 hbErase).2
  have hbCtx : b ∉ ND.fvContext (σ := σ) (sigmaφ :: Γ) := by
    intro hb
    have hSplit :
        b ∈ Syntax.fvFormula (σ := σ) sigmaφ ∨
          b ∈ ND.fvContext (σ := σ) Γ := by
      simpa [ND.fvContext] using hb
    rcases hSplit with hSigma | hTail
    · exact hbSigma hSigma
    · exact hbΓ hTail
  have hSubImp : Γ ⊆ (θb :: sigmaφ :: Γ) := by
    intro ψ hψ
    exact by simp [hψ]
  have hImpBig : Derives (σ := σ) (θb :: sigmaφ :: Γ) (.imp θb χ) :=
    Derives.wk hImpDer hSubImp
  have hHypθb : Derives (σ := σ) (θb :: sigmaφ :: Γ) θb :=
    Derives.hyp (by simp)
  have hDerBig : Derives (σ := σ) (θb :: sigmaφ :: Γ) χ :=
    Derives.impE hImpBig hHypθb
  have hSigmaHyp : Derives (σ := σ) (sigmaφ :: Γ) sigmaφ :=
    Derives.hyp (by simp)
  have hDerSigma : Derives (σ := σ) (sigmaφ :: Γ) χ :=
    Derives.sigmaE hSigmaHyp hbCtx hbVars hbχ hDerBig
  have hDerivMChi : Derivable (σ := σ) M χ := by
    refine ⟨sigmaφ :: Γ, ?_, hDerSigma⟩
    intro ψ hψ
    rcases List.mem_cons.1 hψ with rfl | hψΓ
    · exact hSigmaMemM
    · exact hΓM ψ hψΓ
  exact hMF.2.2 hDerivMChi

theorem not_hasFreshDerivesEFreshImpOnFamily_of_nonempty
    [Nonempty σ] :
    ¬ HasFreshDerivesEFreshImpOnFamily (σ := σ) := by
  exact not_hasFreshDerivesEFreshImpOnFamily (σ := σ)

theorem not_hasFreshSigmaConsFromInsertOnFamily
    :
    ¬ HasFreshSigmaConsFromInsertOnFamily (σ := σ) := by
  intro hFresh
  letI : HasFreshSigmaConsFromInsertOnFamily (σ := σ) := hFresh
  have hImp : HasFreshDerivesEFreshImpOnFamily (σ := σ) :=
    hasFreshDerivesEFreshImpOnFamily_of_freshCons (σ := σ)
  exact not_hasFreshDerivesEFreshImpOnFamily (σ := σ) hImp

/--
Construct the `DerivesEFresh` implication extraction interface from:
- the focused tail-fresh extraction artifact.

The `Derives -> DerivesEFresh` lift is discharged internally via
`ND.DerivesEFresh.ofDerives`.
-/
theorem hasFreshDerivesEFreshImpOnFamily_of_tailFresh
    [HasTailFreshSigmaConsOnFamily (σ := σ)] :
    HasFreshDerivesEFreshImpOnFamily (σ := σ) := by
  refine ⟨?_⟩
  intro S χ M x a φ hMF hMax haVars haχ hχIns
  rcases HasTailFreshSigmaConsOnFamily.tail_fresh_cons_of_derivable_insert
    (σ := σ) (S := S) (χ := χ) (M := M) (x := x) (a := a) (φ := φ)
    hMF hMax haVars haχ hχIns with
    ⟨Γ, haΓ, hΓM, hDerCons⟩
  rcases Lindenbaum.derives_witness_change_to_freshSigmaEigen
    (σ := σ) (Γ := Γ) (x := x) (a := a) (φ := φ) (χ := χ)
    haΓ haVars haχ hDerCons with
    ⟨b, hbΓ, hbVars, hbχ, hDerB⟩
  let θb : Formula σ := Syntax.substFormula (σ := σ) x (.var b) φ
  have hDerImp : Derives (σ := σ) Γ (.imp θb χ) :=
    Derives.impI (by simpa [θb] using hDerB)
  refine ⟨b, Γ, hbVars, hbχ, hΓM, ?_⟩
  exact ND.DerivesEFresh.ofDerives (σ := σ) hbΓ hDerImp

instance (priority := 95)
    hasFreshDerivesEFreshImpOnFamily_of_tailFresh_inst
    [HasTailFreshSigmaConsOnFamily (σ := σ)] :
    HasFreshDerivesEFreshImpOnFamily (σ := σ) := by
  exact hasFreshDerivesEFreshImpOnFamily_of_tailFresh (σ := σ)

-- This route is intentionally not used by default typeclass search.
attribute [-instance] hasFreshDerivesEFreshImpOnFamily_of_tailFresh_inst

/--
The tail-fresh extraction route is also inconsistent on inhabited predicate signatures.

Reason: tail-fresh extraction implies the stronger `DerivesEFresh` implication extraction route,
which is refuted by `not_hasFreshDerivesEFreshImpOnFamily_of_nonempty`.
-/
theorem not_hasTailFreshSigmaConsOnFamily
    :
    ¬ HasTailFreshSigmaConsOnFamily (σ := σ) := by
  intro hTailFresh
  letI : HasTailFreshSigmaConsOnFamily (σ := σ) := hTailFresh
  have hImp : HasFreshDerivesEFreshImpOnFamily (σ := σ) :=
    hasFreshDerivesEFreshImpOnFamily_of_tailFresh (σ := σ)
  exact not_hasFreshDerivesEFreshImpOnFamily (σ := σ) hImp

theorem not_hasFreshSigmaConsFromInsertOnFamily_of_nonempty
    [Nonempty σ] :
    ¬ HasFreshSigmaConsFromInsertOnFamily (σ := σ) := by
  exact not_hasFreshSigmaConsFromInsertOnFamily (σ := σ)

theorem not_hasTailFreshSigmaConsOnFamily_of_nonempty
    [Nonempty σ] :
    ¬ HasTailFreshSigmaConsOnFamily (σ := σ) := by
  exact not_hasTailFreshSigmaConsOnFamily (σ := σ)

/--
Construct the focused tail-fresh extraction obligation from a local source-fresh extractor.
-/
theorem hasTailFreshSigmaConsOnFamily_of_sourceFresh
    (hWeak :
      ∀ {Γ Δ : List (Formula σ)} {φ : Formula σ},
        Derives (σ := σ) Γ φ →
        Γ ⊆ Δ →
        Derives (σ := σ) Δ φ)
    (hSourceFresh :
      ∀ {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)}
        {x a : Var} {φ : Formula σ},
        M ∈ Lindenbaum.Family (σ := σ) S χ →
        Maximal (· ∈ Lindenbaum.Family (σ := σ) S χ) M →
        a ∉ Syntax.varsFormula (σ := σ) φ →
        a ∉ Syntax.fvFormula (σ := σ) χ →
        Derivable (σ := σ) (Set.insert (Syntax.substFormula (σ := σ) x (.var a) φ) M) χ →
        ∀ Γ : List (Formula σ),
          (∀ ψ ∈ Γ, ψ ∈ M) →
          Derives (σ := σ) (Syntax.substFormula (σ := σ) x (.var a) φ :: Γ) χ →
          a ∉ ND.fvContext (σ := σ) Γ) :
    HasTailFreshSigmaConsOnFamily (σ := σ) := by
  refine ⟨?_⟩
  intro S χ M x a φ hMF hMax haVars haχ hχIns
  rcases Lindenbaum.derives_cons_of_derivable_insert
    (σ := σ)
    (T := M)
    (θ := Syntax.substFormula (σ := σ) x (.var a) φ)
    (χ := χ)
    hWeak hχIns with
    ⟨Γ, hΓM, hDerCons⟩
  refine ⟨Γ, ?_, hΓM, hDerCons⟩
  exact hSourceFresh
    (S := S) (χ := χ) (M := M) (x := x) (a := a) (φ := φ)
    hMF hMax haVars haχ hχIns Γ hΓM hDerCons

/--
Construct the focused tail-fresh extraction obligation from a theory-freshness hypothesis.
-/
theorem hasTailFreshSigmaConsOnFamily_of_theoryFresh
    (hWeak :
      ∀ {Γ Δ : List (Formula σ)} {φ : Formula σ},
        Derives (σ := σ) Γ φ →
        Γ ⊆ Δ →
        Derives (σ := σ) Δ φ)
    (hTheoryFresh :
      ∀ {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)} {a : Var},
        M ∈ Lindenbaum.Family (σ := σ) S χ →
        Maximal (· ∈ Lindenbaum.Family (σ := σ) S χ) M →
        a ∉ Syntax.fvFormula (σ := σ) χ →
        ∀ ψ, ψ ∈ M → a ∉ Syntax.fvFormula (σ := σ) ψ) :
    HasTailFreshSigmaConsOnFamily (σ := σ) := by
  refine hasTailFreshSigmaConsOnFamily_of_sourceFresh
    (σ := σ) hWeak ?_
  intro S χ M x a φ hMF hMax _haVars haχ hχIns Γ hΓM hDer
  have hSourceFresh :
      ∀ Γ : List (Formula σ),
        (∀ ψ ∈ Γ, ψ ∈ M) →
        a ∉ ND.fvContext (σ := σ) Γ :=
    Lindenbaum.source_fresh_context_of_subset_theory_fresh
      (σ := σ) (T := M) (a := a)
      (hTheoryFresh (S := S) (χ := χ) (M := M) (a := a) hMF hMax haχ)
  exact hSourceFresh Γ hΓM

/--
Construct the focused tail-fresh extraction obligation from theory closure.
-/
theorem hasTailFreshSigmaConsOnFamily_of_theoryClosed
    (hWeak :
      ∀ {Γ Δ : List (Formula σ)} {φ : Formula σ},
        Derives (σ := σ) Γ φ →
        Γ ⊆ Δ →
        Derives (σ := σ) Δ φ)
    (hTheoryClosed :
      ∀ {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)},
        M ∈ Lindenbaum.Family (σ := σ) S χ →
        Maximal (· ∈ Lindenbaum.Family (σ := σ) S χ) M →
        ∀ ψ, ψ ∈ M → Syntax.fvFormula (σ := σ) ψ = ∅) :
    HasTailFreshSigmaConsOnFamily (σ := σ) := by
  refine hasTailFreshSigmaConsOnFamily_of_theoryFresh
    (σ := σ) hWeak ?_
  intro S χ M a hMF hMax haχ ψ hψ ha
  simp [hTheoryClosed (S := S) (χ := χ) (M := M) hMF hMax ψ hψ] at ha

/--
Construct the full family-level fresh-cons obligation from the focused tail-fresh extraction
artifact.
-/
theorem hasFreshSigmaConsFromInsertOnFamily_of_tailFresh
    [HasTailFreshSigmaConsOnFamily (σ := σ)] :
    HasFreshSigmaConsFromInsertOnFamily (σ := σ) := by
  letI : HasFreshDerivesEFreshImpOnFamily (σ := σ) :=
    hasFreshDerivesEFreshImpOnFamily_of_tailFresh (σ := σ)
  exact hasFreshSigmaConsFromInsertOnFamily_of_derivesEFreshImp (σ := σ)

/--
Construct the family-level fresh-cons obligation from a local source-fresh extractor.

This theorem isolates the final quantifier blocker to one proof task:
showing source freshness of extracted finite contexts for inserted witness derivations.
-/
theorem hasFreshSigmaConsFromInsertOnFamily_of_sourceFresh
    (hWeak :
      ∀ {Γ Δ : List (Formula σ)} {φ : Formula σ},
        Derives (σ := σ) Γ φ →
        Γ ⊆ Δ →
        Derives (σ := σ) Δ φ)
    (hSourceFresh :
      ∀ {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)}
        {x a : Var} {φ : Formula σ},
        M ∈ Lindenbaum.Family (σ := σ) S χ →
        Maximal (· ∈ Lindenbaum.Family (σ := σ) S χ) M →
        a ∉ Syntax.varsFormula (σ := σ) φ →
        a ∉ Syntax.fvFormula (σ := σ) χ →
        Derivable (σ := σ) (Set.insert (Syntax.substFormula (σ := σ) x (.var a) φ) M) χ →
        ∀ Γ : List (Formula σ),
          (∀ ψ ∈ Γ, ψ ∈ M) →
          Derives (σ := σ) (Syntax.substFormula (σ := σ) x (.var a) φ :: Γ) χ →
          a ∉ ND.fvContext (σ := σ) Γ) :
    HasFreshSigmaConsFromInsertOnFamily (σ := σ) := by
  letI : HasTailFreshSigmaConsOnFamily (σ := σ) :=
    hasTailFreshSigmaConsOnFamily_of_sourceFresh
      (σ := σ) hWeak hSourceFresh
  exact hasFreshSigmaConsFromInsertOnFamily_of_tailFresh (σ := σ)

/--
Construct the family-level fresh-cons obligation from a theory-level freshness hypothesis.
-/
theorem hasFreshSigmaConsFromInsertOnFamily_of_theoryFresh
    (hWeak :
      ∀ {Γ Δ : List (Formula σ)} {φ : Formula σ},
        Derives (σ := σ) Γ φ →
        Γ ⊆ Δ →
        Derives (σ := σ) Δ φ)
    (hTheoryFresh :
      ∀ {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)} {a : Var},
        M ∈ Lindenbaum.Family (σ := σ) S χ →
        Maximal (· ∈ Lindenbaum.Family (σ := σ) S χ) M →
        a ∉ Syntax.fvFormula (σ := σ) χ →
        ∀ ψ, ψ ∈ M → a ∉ Syntax.fvFormula (σ := σ) ψ) :
    HasFreshSigmaConsFromInsertOnFamily (σ := σ) := by
  letI : HasTailFreshSigmaConsOnFamily (σ := σ) :=
    hasTailFreshSigmaConsOnFamily_of_theoryFresh
      (σ := σ) hWeak hTheoryFresh
  exact hasFreshSigmaConsFromInsertOnFamily_of_tailFresh (σ := σ)

/--
Construct the family-level fresh-cons obligation from theory closure.

If every formula in maximal family members is closed, the source-fresh side condition is immediate.
-/
theorem hasFreshSigmaConsFromInsertOnFamily_of_theoryClosed
    (hWeak :
      ∀ {Γ Δ : List (Formula σ)} {φ : Formula σ},
        Derives (σ := σ) Γ φ →
        Γ ⊆ Δ →
        Derives (σ := σ) Δ φ)
    (hTheoryClosed :
      ∀ {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)},
        M ∈ Lindenbaum.Family (σ := σ) S χ →
        Maximal (· ∈ Lindenbaum.Family (σ := σ) S χ) M →
        ∀ ψ, ψ ∈ M → Syntax.fvFormula (σ := σ) ψ = ∅) :
    HasFreshSigmaConsFromInsertOnFamily (σ := σ) := by
  letI : HasTailFreshSigmaConsOnFamily (σ := σ) :=
    hasTailFreshSigmaConsOnFamily_of_theoryClosed
      (σ := σ) hWeak hTheoryClosed
  exact hasFreshSigmaConsFromInsertOnFamily_of_tailFresh (σ := σ)

theorem hasWitnessInsertionFamily_of_complete_and_freshCons
    (hWeak :
      ∀ {Γ Δ : List (Formula σ)} {φ : Formula σ},
        Derives (σ := σ) Γ φ →
        Γ ⊆ Δ →
        Derives (σ := σ) Δ φ)
    [HasFreshSigmaConsFromInsertOnFamily (σ := σ)] :
    HasWitnessInsertionFamily (σ := σ) := by
  refine ⟨?_⟩
  intro S χ M hMF hMax x φ hSigmaMem
  let a : Var := ND.freshSigmaEigen (σ := σ) [] φ χ
  let θ : Formula σ := Syntax.substFormula (σ := σ) x (.var a) φ
  have haVars : a ∉ Syntax.varsFormula (σ := σ) φ := by
    simpa using ND.freshSigmaEigen_not_mem_varsFormula (σ := σ) ([] : List (Formula σ)) φ χ
  have haχ : a ∉ Syntax.fvFormula (σ := σ) χ := by
    simpa using ND.freshSigmaEigen_not_mem_fvFormula (σ := σ) ([] : List (Formula σ)) φ χ
  have hFamIns : Set.insert θ M ∈ Lindenbaum.Family (σ := σ) S χ := by
    by_contra hNotFamIns
    have hDerIns : Derivable (σ := σ) (Set.insert θ M) χ :=
      Lindenbaum.derivable_chi_of_not_family (σ := σ) (S := S) (χ := χ) (M := M)
        (θ := θ) hMF hNotFamIns
    rcases HasFreshSigmaConsFromInsertOnFamily.fresh_cons_of_derivable_insert
      (σ := σ) (S := S) (χ := χ) (M := M) (x := x) (a := a) (φ := φ)
      hMF hMax haVars haχ hDerIns with
      ⟨b, Γ, hbΓ, hbVars, hbχ, hΓM, hDerCons⟩
    let θb : Formula σ := Syntax.substFormula (σ := σ) x (.var b) φ
    have hSubCtx : (θb :: Γ) ⊆ (θb :: (.sigma x φ) :: Γ) := by
      intro ψ hψ
      rcases List.mem_cons.1 hψ with rfl | hψΓ
      · simp
      · exact by simp [hψΓ]
    have hDerCons' : Derives (σ := σ) (θb :: (.sigma x φ) :: Γ) χ :=
      hWeak hDerCons hSubCtx
    have hbFvφ : b ∉ Syntax.fvFormula (σ := σ) φ :=
      Syntax.not_mem_fvFormula_of_not_mem_varsFormula (σ := σ) (a := b) (φ := φ) hbVars
    have hbFvSigma : b ∉ Syntax.fvFormula (σ := σ) (.sigma x φ) := by
      intro hb
      exact hbFvφ ((Finset.mem_erase.1 hb).2)
    have hbCtx : b ∉ ND.fvContext (σ := σ) (.sigma x φ :: Γ) := by
      intro hb
      have hsplit : b ∈ Syntax.fvFormula (σ := σ) (.sigma x φ) ∨ b ∈ ND.fvContext (σ := σ) Γ := by
        simpa [ND.fvContext] using hb
      rcases hsplit with hSigma | hTail
      · exact hbFvSigma hSigma
      · exact hbΓ hTail
    have hDerSigma : Derives (σ := σ) (.sigma x φ :: Γ) (.sigma x φ) :=
      Derives.hyp (by simp)
    have hDerGammaChi : Derives (σ := σ) (.sigma x φ :: Γ) χ :=
      Derives.sigmaE hDerSigma hbCtx hbVars hbχ hDerCons'
    have hDerivMχ : Derivable (σ := σ) M χ := by
      refine ⟨.sigma x φ :: Γ, ?_, hDerGammaChi⟩
      intro t ht
      rcases List.mem_cons.1 ht with rfl | htΓ
      · exact hSigmaMem
      · exact hΓM t htΓ
    exact hMF.2.2 hDerivMχ
  exact ⟨a, haVars, hFamIns⟩

/--
Finite-support hypothesis for maximal Lindenbaum members.

For each maximal member in `Family S χ`, there is a finite variable support set that covers the
`varsFormula` footprint of every member formula.
-/
class HasFiniteSupportFamily : Prop where
  support :
    ∀ {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)},
      M ∈ Lindenbaum.Family (σ := σ) S χ →
      Maximal (· ∈ Lindenbaum.Family (σ := σ) S χ) M →
      ∃ E : Finset Var, ∀ ψ, ψ ∈ M → Syntax.varsFormula (σ := σ) ψ ⊆ E

/--
`HasFiniteSupportFamily` is inconsistent in the open FO setting.

Take `S = {∃ var n | n : Var}` and `χ = ⊥`. Any maximal `M ∈ Family S χ` must contain every
`∃ var n`, so no finite support set can cover `varsFormula` of all members.
-/
theorem not_hasFiniteSupportFamily :
    ¬ HasFiniteSupportFamily (σ := σ) := by
  classical
  intro hFinite
  letI : HasFiniteSupportFamily (σ := σ) := hFinite
  let χ : Formula σ := (.bot : Formula σ)
  let S : Set (Formula σ) :=
    fun ψ => ∃ n : Var, ψ = (.eExists (.var n) : Formula σ)
  have hNoDerBot : ¬ Derivable (σ := σ) S χ := by
    intro hDerBot
    rcases hDerBot with ⟨Γ, hΓS, hDerΓBot⟩
    let M0 : Model PUnit σ Var := {
      valPred := fun _ _ _ => True
      monoPred := by
        intro _ _ _ _ _ _
        trivial
      valEx := fun _ _ => True
      monoEx := by
        intro _ _ _ _ h
        exact h
    }
    let ρ : Valuation Var := fun v => v
    have hCtx : ∀ θ ∈ Γ, Forces M0 ρ PUnit.unit θ := by
      intro θ hθ
      rcases hΓS θ hθ with ⟨n, rfl⟩
      simp [Forces, M0]
    have hBotForce : Forces M0 ρ PUnit.unit (.bot : Formula σ) :=
      KripkeFO.soundness (σ := σ) hDerΓBot
        (W := PUnit) (D := Var) (M := M0) (ρ := ρ) (w := PUnit.unit) hCtx
    exact hBotForce
  have hSCons : Consistent (σ := σ) S := hNoDerBot
  rcases Lindenbaum.exists_maximal (σ := σ) (S := S) (χ := χ) hSCons hNoDerBot with
    ⟨M, hSM, hMax⟩
  have hMF : M ∈ Lindenbaum.Family (σ := σ) S χ := hMax.prop
  rcases HasFiniteSupportFamily.support (σ := σ) (S := S) (χ := χ) (M := M) hMF hMax with
    ⟨E, hSupp⟩
  let n : Var := Syntax.freshVar E
  let θ : Formula σ := (.eExists (.var n) : Formula σ)
  have hθS : θ ∈ S := by
    exact ⟨n, rfl⟩
  have hθM : θ ∈ M := hSM hθS
  have hSub : Syntax.varsFormula (σ := σ) θ ⊆ E := hSupp θ hθM
  have hnVars : n ∈ Syntax.varsFormula (σ := σ) θ := by
    simp [θ, Syntax.varsFormula, Syntax.fvTerm]
  have hnE : n ∈ E := hSub hnVars
  exact (Syntax.freshVar_not_mem (S := E)) hnE

/--
Derive the global variable-freshness witness required for witness insertion from finite support.
-/
theorem globalVarFresh_of_finiteSupportFamily
    [HasFiniteSupportFamily (σ := σ)] :
    ∀ {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)},
      M ∈ Lindenbaum.Family (σ := σ) S χ →
      Maximal (· ∈ Lindenbaum.Family (σ := σ) S χ) M →
      ∃ a : Var,
        a ∉ Syntax.fvFormula (σ := σ) χ ∧
        (∀ ψ, ψ ∈ M → a ∉ Syntax.varsFormula (σ := σ) ψ) := by
  intro S χ M hMF hMax
  rcases HasFiniteSupportFamily.support (σ := σ) (S := S) (χ := χ) (M := M) hMF hMax with
    ⟨E, hSupp⟩
  let avoid : Finset Var := E ∪ Syntax.fvFormula (σ := σ) χ
  let a : Var := Syntax.freshVar avoid
  refine ⟨a, ?_, ?_⟩
  · intro haχ
    have haAvoid : a ∉ avoid := Syntax.freshVar_not_mem (S := avoid)
    exact haAvoid (by simp [avoid, haχ])
  · intro ψ hψ haψ
    have hSub : Syntax.varsFormula (σ := σ) ψ ⊆ E := hSupp ψ hψ
    have haE : a ∈ E := hSub haψ
    have haAvoid : a ∉ avoid := Syntax.freshVar_not_mem (S := avoid)
    exact haAvoid (by simp [avoid, haE])

/--
Construct witness-insertion directly from a global variable-freshness fact on maximal members.

This bypasses source-fresh extraction: if a maximal Lindenbaum member has one variable `a` that is
fresh for `χ` and absent from `varsFormula` of every member formula, then sigma-witness insertion
can be discharged in one step.
-/
theorem hasWitnessInsertionFamily_of_openWeakening_globalVarFresh
    [HasOpenWeakening (σ := σ)]
    (hGlobalVarFresh :
      ∀ {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)},
        M ∈ Lindenbaum.Family (σ := σ) S χ →
        Maximal (· ∈ Lindenbaum.Family (σ := σ) S χ) M →
        ∃ a : Var,
          a ∉ Syntax.fvFormula (σ := σ) χ ∧
          (∀ ψ, ψ ∈ M → a ∉ Syntax.varsFormula (σ := σ) ψ)) :
    HasWitnessInsertionFamily (σ := σ) := by
  refine ⟨?_⟩
  intro S χ M hMF hMax x φ hSigmaMem
  rcases hGlobalVarFresh (S := S) (χ := χ) (M := M) hMF hMax with ⟨a, haχ, hVarsM⟩
  have haVarsSigma : a ∉ Syntax.varsFormula (σ := σ) (.sigma x φ) := hVarsM (.sigma x φ) hSigmaMem
  have haVars : a ∉ Syntax.varsFormula (σ := σ) φ := by
    intro ha
    exact haVarsSigma (by simp [Syntax.varsFormula, ha])
  let θ : Formula σ := Syntax.substFormula (σ := σ) x (.var a) φ
  have hFamIns : Set.insert θ M ∈ Lindenbaum.Family (σ := σ) S χ := by
    by_contra hNotFamIns
    have hDerIns : Derivable (σ := σ) (Set.insert θ M) χ :=
      Lindenbaum.derivable_chi_of_not_family (σ := σ) (S := S) (χ := χ) (M := M)
        (θ := θ) hMF hNotFamIns
    rcases Lindenbaum.derives_cons_of_derivable_insert
      (σ := σ) (T := M) (θ := θ) (χ := χ)
      (HasOpenWeakening.weaken (σ := σ)) hDerIns with
      ⟨Γ, hΓM, hDerCons⟩
    have haΓ : a ∉ ND.fvContext (σ := σ) Γ := by
      intro haΓMem
      rcases (ND.mem_fvContext_iff (σ := σ) (x := a) (Γ := Γ)).1 haΓMem with ⟨ψ, hψΓ, haψ⟩
      have haVarsψ : a ∉ Syntax.varsFormula (σ := σ) ψ := hVarsM ψ (hΓM ψ hψΓ)
      exact (Syntax.not_mem_fvFormula_of_not_mem_varsFormula (σ := σ) (a := a) (φ := ψ) haVarsψ) haψ
    have haFvSigma : a ∉ Syntax.fvFormula (σ := σ) (.sigma x φ) := by
      exact Syntax.not_mem_fvFormula_of_not_mem_varsFormula
        (σ := σ) (a := a) (φ := (.sigma x φ)) haVarsSigma
    have hSubCtx : (θ :: Γ) ⊆ (θ :: (.sigma x φ) :: Γ) := by
      intro ψ hψ
      rcases List.mem_cons.1 hψ with rfl | hψΓ
      · simp
      · exact by simp [hψΓ]
    have hDerCons' : Derives (σ := σ) (θ :: (.sigma x φ) :: Γ) χ :=
      HasOpenWeakening.weaken (σ := σ) hDerCons hSubCtx
    have hCtx : a ∉ ND.fvContext (σ := σ) (.sigma x φ :: Γ) := by
      intro haMem
      have hsplit :
          a ∈ Syntax.fvFormula (σ := σ) (.sigma x φ) ∨ a ∈ ND.fvContext (σ := σ) Γ := by
        simpa [ND.fvContext] using haMem
      rcases hsplit with hSigma | hTail
      · exact haFvSigma hSigma
      · exact haΓ hTail
    have hDerSigma : Derives (σ := σ) (.sigma x φ :: Γ) (.sigma x φ) :=
      Derives.hyp (by simp)
    have hDerGammaChi : Derives (σ := σ) (.sigma x φ :: Γ) χ :=
      Derives.sigmaE hDerSigma hCtx haVars haχ hDerCons'
    have hDerivMχ : Derivable (σ := σ) M χ := by
      refine ⟨.sigma x φ :: Γ, ?_, hDerGammaChi⟩
      intro ψ hψ
      rcases List.mem_cons.1 hψ with rfl | hψΓ
      · exact hSigmaMem
      · exact hΓM ψ hψΓ
    exact hMF.2.2 hDerivMχ
  exact ⟨a, haVars, hFamIns⟩

/--
Construct witness insertion from open weakening plus finite support on maximal Lindenbaum members.
-/
theorem hasWitnessInsertionFamily_of_openWeakening_finiteSupport
    [HasOpenWeakening (σ := σ)]
    [HasFiniteSupportFamily (σ := σ)] :
    HasWitnessInsertionFamily (σ := σ) := by
  exact hasWitnessInsertionFamily_of_openWeakening_globalVarFresh
    (σ := σ)
    (hGlobalVarFresh := globalVarFresh_of_finiteSupportFamily (σ := σ))

instance (priority := 92)
    hasHenkinSigmaPromotion_of_witnessInsertionFamily
    [HasWitnessInsertionFamily (σ := σ)] :
    HasHenkinSigmaPromotion (σ := σ) where
  sigma_witness_of_maximal := by
    intro S χ M hMF hMax x φ hSigmaMem
    rcases HasWitnessInsertionFamily.insert_sigma_witness_family
      (σ := σ) (S := S) (χ := χ) (M := M) hMF hMax hSigmaMem with
      ⟨a, haVars, hFamIns⟩
    let θ : Formula σ := Syntax.substFormula (σ := σ) x (.var a) φ
    have hSub : M ⊆ Set.insert θ M := by
      intro t ht
      exact Or.inr ht
    have hEq : Set.insert θ M = M := (hMax.eq_of_subset hFamIns hSub).symm
    have hθMem : θ ∈ M := by
      have : θ ∈ Set.insert θ M := Or.inl rfl
      simpa [hEq] using this
    exact ⟨a, haVars, hθMem⟩

instance (priority := 90)
    hasExtensionConstruction_of_lindenbaum_promotion
    [HasSequentFamilyBase (σ := σ)]
    [HasSaturatedPromotion (σ := σ)] :
    HasExtensionConstruction (σ := σ) where
  extend_avoid := by
    intro Γ φ hNotDer
    let S : Set (Formula σ) := fun ψ => ψ ∈ Γ
    have hSCons : Consistent (σ := σ) S :=
      HasSequentFamilyBase.base_consistent (σ := σ) (Γ := Γ) (φ := φ) hNotDer
    have hSNot : ¬ Derivable (σ := σ) S φ :=
      HasSequentFamilyBase.base_notDerivable (σ := σ) (Γ := Γ) (φ := φ) hNotDer
    rcases Lindenbaum.exists_maximal (σ := σ) S φ hSCons hSNot with ⟨M, hSM, hMax⟩
    have hMF : M ∈ Lindenbaum.Family (σ := σ) S φ := hMax.prop
    rcases HasSaturatedPromotion.of_maximal (σ := σ) (S := S) (χ := φ) (M := M) hMF hMax with
      ⟨w, hSw, hNotMem⟩
    refine ⟨w, ?_, hNotMem⟩
    intro ψ hψ
    exact hSw (by simpa [S] using hψ)

/-- Internal obligation B: canonical truth lemma (`Forces` iff membership). -/
class HasTruthLemma : Prop where
  truth_iff_mem :
    ∀ (w : W (σ := σ)) (ψ : Formula σ),
      Forces (canonicalModel (σ := σ)) idVarValuation w ψ ↔ ψ ∈ w.carrier

/--
Counterexample obligations for the canonical implication/negation cases.

These are the exact Lindenbaum-style extension properties needed to prove the full
canonical truth lemma by structural recursion.
-/
class HasCanonicalNegImpExtensions : Prop where
  not_counterexample :
    ∀ {w : W (σ := σ)} {φ : Formula σ},
      (.not φ) ∉ w.carrier →
        ∃ v : W (σ := σ), w ≤ v ∧ φ ∈ v.carrier
  imp_counterexample :
    ∀ {w : W (σ := σ)} {φ ψ : Formula σ},
      (.imp φ ψ) ∉ w.carrier →
        ∃ v : W (σ := σ), w ≤ v ∧ φ ∈ v.carrier ∧ ψ ∉ v.carrier

/--
Build canonical neg/imp counterexample extensions from:
- unrestricted weakening in `Derives`,
- saturated-world promotion from maximal Lindenbaum members.

This discharges the propositional extension obligations internally, leaving only quantifier truth
as the final canonical artifact.
-/
theorem hasCanonicalNegImpExtensions_of_openWeakening_saturatedPromotion
    [HasOpenWeakening (σ := σ)]
    [HasSaturatedPromotion (σ := σ)] :
    HasCanonicalNegImpExtensions (σ := σ) := by
  refine ⟨?_, ?_⟩
  · intro w φ hNotMem
    have hConsIns : Consistent (σ := σ) (Set.insert φ w.carrier) := by
      intro hBotIns
      rcases Lindenbaum.derives_cons_of_derivable_insert
        (σ := σ) (T := w.carrier) (θ := φ) (χ := (.bot : Formula σ))
        (HasOpenWeakening.weaken (σ := σ)) hBotIns with
        ⟨Γ, hΓw, hDerConsBot⟩
      have hNotDer : Derivable (σ := σ) w.carrier (.not φ) := by
        exact ⟨Γ, hΓw, Derives.notI hDerConsBot⟩
      exact hNotMem (w.closed _ hNotDer)
    have hNoDerBot : ¬ Derivable (σ := σ) (Set.insert φ w.carrier) (.bot : Formula σ) :=
      hConsIns
    rcases Lindenbaum.exists_maximal
      (σ := σ) (S := Set.insert φ w.carrier) (χ := (.bot : Formula σ))
      hConsIns hNoDerBot with
      ⟨M, _hSM, hMax⟩
    have hMF : M ∈ Lindenbaum.Family (σ := σ) (Set.insert φ w.carrier) (.bot : Formula σ) :=
      hMax.prop
    rcases HasSaturatedPromotion.of_maximal
      (σ := σ)
      (S := Set.insert φ w.carrier)
      (χ := (.bot : Formula σ))
      (M := M) hMF hMax with
      ⟨v, hSv, _hBotNotMem⟩
    refine ⟨v, ?_, ?_⟩
    · intro θ hθ
      exact hSv (Or.inr hθ)
    · exact hSv (Or.inl rfl)
  · intro w φ ψ hImpNotMem
    have hNoDerPsi :
        ¬ Derivable (σ := σ) (Set.insert φ w.carrier) ψ := by
      intro hDerPsi
      have hImpDer : Derivable (σ := σ) w.carrier (.imp φ ψ) :=
        Lindenbaum.derivable_imp_of_derivable_insert
          (σ := σ) (T := w.carrier) (θ := φ) (χ := ψ)
          (HasOpenWeakening.weaken (σ := σ)) hDerPsi
      exact hImpNotMem (w.closed _ hImpDer)
    have hConsIns : Consistent (σ := σ) (Set.insert φ w.carrier) := by
      intro hBotIns
      have hDerPsi : Derivable (σ := σ) (Set.insert φ w.carrier) ψ := by
        rcases hBotIns with ⟨Γ, hΓIns, hDerBot⟩
        exact ⟨Γ, hΓIns, Derives.botE hDerBot⟩
      exact hNoDerPsi hDerPsi
    rcases Lindenbaum.exists_maximal
      (σ := σ) (S := Set.insert φ w.carrier) (χ := ψ)
      hConsIns hNoDerPsi with
      ⟨M, _hSM, hMax⟩
    have hMF : M ∈ Lindenbaum.Family (σ := σ) (Set.insert φ w.carrier) ψ := hMax.prop
    rcases HasSaturatedPromotion.of_maximal
      (σ := σ) (S := Set.insert φ w.carrier) (χ := ψ) (M := M) hMF hMax with
      ⟨v, hSv, hPsiNotMem⟩
    refine ⟨v, ?_, ?_, hPsiNotMem⟩
    · intro θ hθ
      exact hSv (Or.inr hθ)
    · exact hSv (Or.inl rfl)

/--
Quantifier-specific obligations that remain after the core canonical recursion is in place.

`sigma`/`pi` are now reduced to:
- truth of strictly smaller formulas (for instantiated bodies), and
- `pi` generalization from all instances.
-/
class HasCanonicalQuantifierTruth : Prop where
  sigma_forces_iff_mem :
    ∀ (w : W (σ := σ)) (x : Var) (φ : Formula σ),
      Forces (canonicalModel (σ := σ)) idVarValuation w (.sigma x φ) ↔
        (.sigma x φ : Formula σ) ∈ w.carrier
  pi_forces_iff_mem :
    ∀ (w : W (σ := σ)) (x : Var) (φ : Formula σ),
      Forces (canonicalModel (σ := σ)) idVarValuation w (.pi x φ) ↔
        (.pi x φ : Formula σ) ∈ w.carrier

/--
Canonical truth oracle on strictly smaller formulas.

This isolates the remaining well-founded recursion artifact used to close quantifier truth
internally.
-/
class HasCanonicalTruthBySize : Prop where
  truth_lt :
    ∀ (n : Nat) (w : W (σ := σ)) (ψ : Formula σ),
      Syntax.fSize (σ := σ) ψ < n →
        (Forces (canonicalModel (σ := σ)) idVarValuation w ψ ↔ ψ ∈ w.carrier)

set_option linter.unnecessarySimpa false
/--
Internal size-recursive canonical truth lemma from:
- canonical neg/imp counterexample obligations, and
- canonical `pi` generalization.

This is the core internal artifact for quantifier truth: no external quantifier oracle is needed.
-/
theorem canonical_truth_lt_of_negImp_and_piGeneralization
    [HasCanonicalNegImpExtensions (σ := σ)]
    [HasCanonicalPiGeneralization (σ := σ)] :
    ∀ (n : Nat) (w : W (σ := σ)) (ψ : Formula σ),
      Syntax.fSize (σ := σ) ψ < n →
        (Forces (canonicalModel (σ := σ)) idVarValuation w ψ ↔ ψ ∈ w.carrier) := by
  intro n
  induction n with
  | zero =>
      intro w ψ hlt
      exact (Nat.not_lt_zero _ hlt).elim
  | succ n ih =>
      intro w ψ hlt
      have hψLe : Syntax.fSize (σ := σ) ψ ≤ n :=
        Nat.lt_succ_iff.mp hlt
      have hTruthLt :
          ∀ ψ' : Formula σ,
            Syntax.fSize (σ := σ) ψ' < Syntax.fSize (σ := σ) ψ →
              (Forces (canonicalModel (σ := σ)) idVarValuation w ψ' ↔ ψ' ∈ w.carrier) := by
        intro ψ' hlt'
        exact ih w ψ' (Nat.lt_of_lt_of_le hlt' hψLe)
      have hTruthLtExt :
          ∀ v : W (σ := σ), w ≤ v →
            ∀ ψ' : Formula σ,
              Syntax.fSize (σ := σ) ψ' < Syntax.fSize (σ := σ) ψ →
                (Forces (canonicalModel (σ := σ)) idVarValuation v ψ' ↔ ψ' ∈ v.carrier) := by
        intro v _hwv ψ' hlt'
        exact ih v ψ' (Nat.lt_of_lt_of_le hlt' hψLe)
      cases ψ with
      | top =>
          constructor
          · intro _
            have hDer : Derivable (σ := σ) w.carrier (.top : Formula σ) :=
              ⟨[], by simp, Derives.topI⟩
            exact w.closed _ hDer
          · intro _
            trivial
      | bot =>
          constructor
          · intro h
            exact False.elim h
          · intro hMem
            exact (w.consistent (derivable_of_mem (σ := σ) (T := w.carrier) hMem)).elim
      | pred p args =>
          exact canonical_forces_pred_iff_mem (σ := σ) (w := w) p args
      | eExists t =>
          exact canonical_forces_exists_atom_iff_mem (σ := σ) (w := w) t
      | not φ =>
          constructor
          · intro hForce
            by_contra hNotMem
            rcases HasCanonicalNegImpExtensions.not_counterexample (σ := σ) (w := w) (φ := φ) hNotMem with
              ⟨v, hwv, hφMem⟩
            have hφForce : Forces (canonicalModel (σ := σ)) idVarValuation v φ :=
              ((hTruthLtExt v hwv φ (by simp [Syntax.fSize])).2 hφMem)
            exact hForce v hwv hφForce
          · intro hNotMem v hwv hφForce
            have hNotMemV : (.not φ : Formula σ) ∈ v.carrier := hwv hNotMem
            have hφMemV : φ ∈ v.carrier :=
              ((hTruthLtExt v hwv φ (by simp [Syntax.fSize])).1 hφForce)
            have hBotDer : Derivable (σ := σ) v.carrier (.bot : Formula σ) := by
              refine ⟨[.not φ, φ], ?_, ?_⟩
              · intro t ht
                simp at ht
                rcases ht with rfl | rfl
                · exact hNotMemV
                · exact hφMemV
              ·
                have h1 : Derives (σ := σ) [.not φ, φ] (.not φ) := Derives.hyp (by simp)
                have h2 : Derives (σ := σ) [.not φ, φ] φ := Derives.hyp (by simp)
                exact Derives.notE h1 h2
            exact v.consistent hBotDer
      | and φ χ =>
          have hφLt : Syntax.fSize (σ := σ) φ < Syntax.fSize (σ := σ) (.and φ χ) := by
            have h :
                Syntax.fSize (σ := σ) φ <
                  Syntax.fSize (σ := σ) φ + (Syntax.fSize (σ := σ) χ + 1) :=
              Nat.lt_add_of_pos_right (Nat.succ_pos _)
            simpa [Syntax.fSize, Nat.add_assoc] using h
          have hχLt : Syntax.fSize (σ := σ) χ < Syntax.fSize (σ := σ) (.and φ χ) := by
            have h :
                Syntax.fSize (σ := σ) χ <
                  Syntax.fSize (σ := σ) χ + (Syntax.fSize (σ := σ) φ + 1) :=
              Nat.lt_add_of_pos_right (Nat.succ_pos _)
            simpa [Syntax.fSize, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
          constructor
          · intro hForce
            have hφMem : φ ∈ w.carrier :=
              (hTruthLt φ hφLt).1 hForce.1
            have hχMem : χ ∈ w.carrier :=
              (hTruthLt χ hχLt).1 hForce.2
            have hDer : Derivable (σ := σ) w.carrier (.and φ χ) := by
              refine ⟨[φ, χ], ?_, ?_⟩
              · intro t ht
                simp at ht
                rcases ht with rfl | rfl
                · exact hφMem
                · exact hχMem
              ·
                have hφ' : Derives (σ := σ) [φ, χ] φ := Derives.hyp (by simp)
                have hχ' : Derives (σ := σ) [φ, χ] χ := Derives.hyp (by simp)
                exact Derives.andI hφ' hχ'
            exact w.closed _ hDer
          · intro hAndMem
            have hφMem : φ ∈ w.carrier := by
              rcases derivable_of_mem (σ := σ) (T := w.carrier) hAndMem with ⟨Γ, hΓ, hDer⟩
              exact w.closed _ ⟨Γ, hΓ, Derives.andEL hDer⟩
            have hχMem : χ ∈ w.carrier := by
              rcases derivable_of_mem (σ := σ) (T := w.carrier) hAndMem with ⟨Γ, hΓ, hDer⟩
              exact w.closed _ ⟨Γ, hΓ, Derives.andER hDer⟩
            exact And.intro
              ((hTruthLt φ hφLt).2 hφMem)
              ((hTruthLt χ hχLt).2 hχMem)
      | or φ χ =>
          have hφLt : Syntax.fSize (σ := σ) φ < Syntax.fSize (σ := σ) (.or φ χ) := by
            have h :
                Syntax.fSize (σ := σ) φ <
                  Syntax.fSize (σ := σ) φ + (Syntax.fSize (σ := σ) χ + 1) :=
              Nat.lt_add_of_pos_right (Nat.succ_pos _)
            simpa [Syntax.fSize, Nat.add_assoc] using h
          have hχLt : Syntax.fSize (σ := σ) χ < Syntax.fSize (σ := σ) (.or φ χ) := by
            have h :
                Syntax.fSize (σ := σ) χ <
                  Syntax.fSize (σ := σ) χ + (Syntax.fSize (σ := σ) φ + 1) :=
              Nat.lt_add_of_pos_right (Nat.succ_pos _)
            simpa [Syntax.fSize, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
          constructor
          · intro hForce
            cases hForce with
            | inl hφForce =>
                have hφMem : φ ∈ w.carrier :=
                  (hTruthLt φ hφLt).1 hφForce
                have hDer : Derivable (σ := σ) w.carrier (.or φ χ) := by
                  refine ⟨[φ], ?_, ?_⟩
                  · intro t ht
                    simp at ht
                    subst ht
                    exact hφMem
                  ·
                    have hφ' : Derives (σ := σ) [φ] φ := Derives.hyp (by simp)
                    exact Derives.orIL hφ'
                exact w.closed _ hDer
            | inr hχForce =>
                have hχMem : χ ∈ w.carrier :=
                  (hTruthLt χ hχLt).1 hχForce
                have hDer : Derivable (σ := σ) w.carrier (.or φ χ) := by
                  refine ⟨[χ], ?_, ?_⟩
                  · intro t ht
                    simp at ht
                    subst ht
                    exact hχMem
                  ·
                    have hχ' : Derives (σ := σ) [χ] χ := Derives.hyp (by simp)
                    exact Derives.orIR hχ'
                exact w.closed _ hDer
          · intro hOrMem
            rcases w.prime φ χ hOrMem with hφMem | hχMem
            · exact Or.inl ((hTruthLt φ hφLt).2 hφMem)
            · exact Or.inr ((hTruthLt χ hχLt).2 hχMem)
      | imp φ χ =>
          have hφLt : Syntax.fSize (σ := σ) φ < Syntax.fSize (σ := σ) (.imp φ χ) := by
            have h :
                Syntax.fSize (σ := σ) φ <
                  Syntax.fSize (σ := σ) φ + (Syntax.fSize (σ := σ) χ + 1) :=
              Nat.lt_add_of_pos_right (Nat.succ_pos _)
            simpa [Syntax.fSize, Nat.add_assoc] using h
          have hχLt : Syntax.fSize (σ := σ) χ < Syntax.fSize (σ := σ) (.imp φ χ) := by
            have h :
                Syntax.fSize (σ := σ) χ <
                  Syntax.fSize (σ := σ) χ + (Syntax.fSize (σ := σ) φ + 1) :=
              Nat.lt_add_of_pos_right (Nat.succ_pos _)
            simpa [Syntax.fSize, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
          constructor
          · intro hForce
            by_contra hImpMem
            rcases HasCanonicalNegImpExtensions.imp_counterexample (σ := σ) (w := w)
                (φ := φ) (ψ := χ) hImpMem with ⟨v, hwv, hφMem, hχNotMem⟩
            have hφForce : Forces (canonicalModel (σ := σ)) idVarValuation v φ :=
              ((hTruthLtExt v hwv φ hφLt).2 hφMem)
            have hχForce : Forces (canonicalModel (σ := σ)) idVarValuation v χ :=
              hForce v hwv hφForce
            exact hχNotMem ((hTruthLtExt v hwv χ hχLt).1 hχForce)
          · intro hImpMem v hwv hφForce
            have hImpMemV : (.imp φ χ : Formula σ) ∈ v.carrier := hwv hImpMem
            have hφMemV : φ ∈ v.carrier :=
              ((hTruthLtExt v hwv φ hφLt).1 hφForce)
            have hχDer : Derivable (σ := σ) v.carrier χ := by
              refine ⟨[.imp φ χ, φ], ?_, ?_⟩
              · intro t ht
                simp at ht
                rcases ht with rfl | rfl
                · exact hImpMemV
                · exact hφMemV
              ·
                have h1 : Derives (σ := σ) [.imp φ χ, φ] (.imp φ χ) := Derives.hyp (by simp)
                have h2 : Derives (σ := σ) [.imp φ χ, φ] φ := Derives.hyp (by simp)
                exact Derives.impE h1 h2
            have hχMemV : χ ∈ v.carrier := v.closed _ hχDer
            exact (hTruthLtExt v hwv χ hχLt).2 hχMemV
      | sigma x φ =>
          exact canonical_sigma_forces_iff_mem_of_lt
            (σ := σ) (w := w) (x := x) (φ := φ) hTruthLt
      | pi x φ =>
          exact canonical_pi_forces_iff_mem_of_lt_and_generalization_on_extensions
            (σ := σ)
            (w := w) (x := x) (φ := φ)
            (hTruthLt := by
              intro v hwv ψ' hlt'
              exact hTruthLtExt v hwv ψ' hlt')
            (hPiGeneralize := by
              intro v _hwv hAllInst
              exact HasCanonicalPiGeneralization.pi_generalize (σ := σ) v x φ hAllInst)

set_option linter.unnecessarySimpa true

instance (priority := 94)
    hasCanonicalTruthBySize_of_negImp_and_piGeneralization
    [HasCanonicalNegImpExtensions (σ := σ)]
    [HasCanonicalPiGeneralization (σ := σ)] :
    HasCanonicalTruthBySize (σ := σ) where
  truth_lt := by
    intro n w ψ hlt
    exact canonical_truth_lt_of_negImp_and_piGeneralization
      (σ := σ) n w ψ hlt

instance (priority := 95)
    hasCanonicalQuantifierTruth_of_piGeneralization_and_truthBySize
    [HasCanonicalPiGeneralization (σ := σ)]
    [HasCanonicalTruthBySize (σ := σ)] :
    HasCanonicalQuantifierTruth (σ := σ) where
  sigma_forces_iff_mem := by
    intro w x φ
    exact canonical_sigma_forces_iff_mem_of_lt
      (σ := σ) (w := w) (x := x) (φ := φ)
      (hTruthLt := by
        intro ψ hlt
        exact HasCanonicalTruthBySize.truth_lt
          (σ := σ) (n := Syntax.fSize (σ := σ) (.sigma x φ)) (w := w) (ψ := ψ) hlt)
  pi_forces_iff_mem := by
    intro w x φ
    exact canonical_pi_forces_iff_mem_of_lt_and_generalization_on_extensions
      (σ := σ) (w := w) (x := x) (φ := φ)
      (hTruthLt := by
        intro v _hwv ψ hlt
        exact HasCanonicalTruthBySize.truth_lt
          (σ := σ) (n := Syntax.fSize (σ := σ) (.pi x φ)) (w := v) (ψ := ψ) hlt)
      (hPiGeneralize := by
        intro v _hwv hAllInst
        exact HasCanonicalPiGeneralization.pi_generalize (σ := σ) v x φ hAllInst)

/--
Sentence-oriented closure interface for maximal Lindenbaum members.

This is the Track F fallback hook: if maximal members are internally known to contain only
closed formulas, the tail-fresh quantifier extraction obligation is discharged automatically.

Important: this interface is intentionally strong. For genuinely open base theories `S`,
it is not expected to hold globally (see `not_hasSentenceFamilyClosure_of_open_base` below).
-/
class HasSentenceFamilyClosure : Prop where
  theory_closed :
    ∀ {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)},
      M ∈ Lindenbaum.Family (σ := σ) S χ →
      Maximal (· ∈ Lindenbaum.Family (σ := σ) S χ) M →
      ∀ ψ, ψ ∈ M → Syntax.fvFormula (σ := σ) ψ = ∅

/--
`HasSentenceFamilyClosure` cannot hold for an open base theory.

If `S` contains a formula with non-empty free-variable set and admits a maximal Lindenbaum
extension in `Family S χ`, then the global sentence-family closure interface is inconsistent.
-/
theorem not_hasSentenceFamilyClosure_of_open_base
    {S : Set (Formula σ)} {χ : Formula σ}
    (hSCons : Consistent (σ := σ) S)
    (hNoChi : ¬ Derivable (σ := σ) S χ)
    (hOpen : ∃ ψ : Formula σ, ψ ∈ S ∧ Syntax.fvFormula (σ := σ) ψ ≠ ∅) :
    ¬ HasSentenceFamilyClosure (σ := σ) := by
  intro hClosure
  rcases Lindenbaum.exists_maximal (σ := σ) S χ hSCons hNoChi with
    ⟨M, hSM, hMax⟩
  have hMF : M ∈ Lindenbaum.Family (σ := σ) S χ := hMax.prop
  rcases hOpen with ⟨ψ, hψS, hψOpen⟩
  have hψM : ψ ∈ M := hSM hψS
  have hψClosed : Syntax.fvFormula (σ := σ) ψ = ∅ :=
    HasSentenceFamilyClosure.theory_closed
      (σ := σ) (S := S) (χ := χ) (M := M) hMF hMax ψ hψM
  exact hψOpen hψClosed

/--
`HasSentenceFamilyClosure` is globally inconsistent.

This does not require inhabited predicate symbols: the open atom `eExists (.var x)` already
provides an open base theory witness.
-/
theorem not_hasSentenceFamilyClosure :
    ¬ HasSentenceFamilyClosure (σ := σ) := by
  let x : Var := 0
  let θ : Formula σ := (.eExists (.var x) : Formula σ)
  let S : Set (Formula σ) := {θ}
  have hNoBot : ¬ Derivable (σ := σ) S (.bot : Formula σ) := by
    intro hDerBot
    rcases hDerBot with ⟨Γ, hΓS, hDerΓBot⟩
    let M : Model PUnit σ Var := {
      valPred := fun _ _ _ => True
      monoPred := by
        intro _ _ _ _ _ _
        trivial
      valEx := fun _ d => d = x
      monoEx := by
        intro _ _ _ _ h
        exact h
    }
    let ρ : Valuation Var := fun v => v
    have hThetaForce : Forces M ρ PUnit.unit θ := by
      simp [θ, Forces, M, ρ, evalTerm]
    have hΓForce : ∀ ψ ∈ Γ, Forces M ρ PUnit.unit ψ := by
      intro ψ hψ
      have hψS : ψ ∈ S := hΓS ψ hψ
      have hψθ : ψ = θ := by simpa [S] using hψS
      simpa [hψθ] using hThetaForce
    have hBotForce : Forces M ρ PUnit.unit (.bot : Formula σ) :=
      KripkeFO.soundness (σ := σ) hDerΓBot
        (W := PUnit) (D := Var) (M := M) (ρ := ρ) (w := PUnit.unit) hΓForce
    exact hBotForce
  have hSCons : Consistent (σ := σ) S := hNoBot
  have hOpen : ∃ ψ : Formula σ, ψ ∈ S ∧ Syntax.fvFormula (σ := σ) ψ ≠ ∅ := by
    refine ⟨θ, by simp [S], ?_⟩
    have hx : x ∈ Syntax.fvFormula (σ := σ) θ := by
      simp [θ, Syntax.fvFormula, Syntax.fvTerm]
    intro hEmpty
    simp [hEmpty] at hx
  exact not_hasSentenceFamilyClosure_of_open_base
    (σ := σ) (S := S) (χ := (.bot : Formula σ)) hSCons hNoBot hOpen

/--
`HasSentenceFamilyClosure` is inconsistent whenever the predicate signature is inhabited.

Witness theory: `{pred p [x]}` with `x = 0`. It is consistent (soundness in a trivial model)
and open, so `not_hasSentenceFamilyClosure_of_open_base` applies.
-/
theorem not_hasSentenceFamilyClosure_of_nonempty
    [Nonempty σ] :
    ¬ HasSentenceFamilyClosure (σ := σ) := by
  exact not_hasSentenceFamilyClosure (σ := σ)

instance (priority := 94)
    hasTailFreshSigmaConsOnFamily_of_sentenceFamilyClosure
    [HasOpenWeakening (σ := σ)]
    [HasSentenceFamilyClosure (σ := σ)] :
    HasTailFreshSigmaConsOnFamily (σ := σ) := by
  exact hasTailFreshSigmaConsOnFamily_of_theoryClosed
    (σ := σ)
    (hWeak := HasOpenWeakening.weaken (σ := σ))
    (hTheoryClosed := InternalFO.HasSentenceFamilyClosure.theory_closed (σ := σ))

-- This route is intentionally not used by default typeclass search.
attribute [-instance] hasTailFreshSigmaConsOnFamily_of_sentenceFamilyClosure

instance (priority := 94)
    hasFreshSigmaConsFromInsertOnFamily_of_sentenceFamilyClosure
    [HasOpenWeakening (σ := σ)]
    [HasSentenceFamilyClosure (σ := σ)] :
    HasFreshSigmaConsFromInsertOnFamily (σ := σ) := by
  letI : HasTailFreshSigmaConsOnFamily (σ := σ) := by
    exact hasTailFreshSigmaConsOnFamily_of_sentenceFamilyClosure (σ := σ)
  exact hasFreshSigmaConsFromInsertOnFamily_of_tailFresh (σ := σ)

-- This route is intentionally not used by default typeclass search.
attribute [-instance] hasFreshSigmaConsFromInsertOnFamily_of_sentenceFamilyClosure

/--
Derive canonical-world closure from the sentence-family closure interface.

For each canonical world `w`, extend `w.carrier` to a maximal member of
`Lindenbaum.Family w.carrier ⊥`; sentence-family closure at that maximal member
then propagates closure back to formulas already in `w.carrier`.
-/
theorem hasCanonicalTheoryClosed_of_sentenceFamilyClosure
    [HasSentenceFamilyClosure (σ := σ)] :
    HasCanonicalTheoryClosed (σ := σ) := by
  refine ⟨?_⟩
  intro w ψ hψ
  have hCons : Consistent (σ := σ) w.carrier := w.consistent
  have hNoBot : ¬ Derivable (σ := σ) w.carrier (.bot : Formula σ) := w.consistent
  rcases Lindenbaum.exists_maximal
    (σ := σ) (S := w.carrier) (χ := (.bot : Formula σ)) hCons hNoBot with
    ⟨M, hwM, hMax⟩
  have hMF : M ∈ Lindenbaum.Family (σ := σ) w.carrier (.bot : Formula σ) := hMax.prop
  have hClosedM :
      ∀ θ : Formula σ, θ ∈ M → Syntax.fvFormula (σ := σ) θ = ∅ :=
    HasSentenceFamilyClosure.theory_closed
      (σ := σ) (S := w.carrier) (χ := (.bot : Formula σ)) (M := M) hMF hMax
  exact hClosedM ψ (hwM hψ)

instance (priority := 95)
    hasCanonicalPiGeneralization_of_sentenceFamilyClosure
    [HasSentenceFamilyClosure (σ := σ)] :
    HasCanonicalPiGeneralization (σ := σ) := by
  letI : HasCanonicalTheoryClosed (σ := σ) :=
    hasCanonicalTheoryClosed_of_sentenceFamilyClosure (σ := σ)
  infer_instance

-- Keep this as an opt-in bridge; sentence-family closure is a known dead-end on open bases.
attribute [-instance] hasCanonicalPiGeneralization_of_sentenceFamilyClosure

/--
Full canonical truth lemma, decomposed into explicit internal obligations.

This theorem is fully internal for all propositional constructors and `sigma`-forward direction.
Remaining quantifier converse obligations are isolated in `HasCanonicalQuantifierTruth`.
-/
theorem truth_iff_mem_of_obligations
    [HasCanonicalNegImpExtensions (σ := σ)]
    [HasCanonicalQuantifierTruth (σ := σ)] :
    ∀ (w : W (σ := σ)) (ψ : Formula σ),
      Forces (canonicalModel (σ := σ)) idVarValuation w ψ ↔ ψ ∈ w.carrier := by
  intro w ψ
  induction ψ generalizing w with
  | top =>
      constructor
      · intro _
        have hDer : Derivable (σ := σ) w.carrier (.top : Formula σ) :=
          ⟨[], by simp, Derives.topI⟩
        exact w.closed _ hDer
      · intro _
        trivial
  | bot =>
      constructor
      · intro h
        exact False.elim h
      · intro hMem
        exact (w.consistent (derivable_of_mem (σ := σ) (T := w.carrier) hMem)).elim
  | pred p args =>
      exact canonical_forces_pred_iff_mem (σ := σ) (w := w) p args
  | eExists t =>
      exact canonical_forces_exists_atom_iff_mem (σ := σ) (w := w) t
  | not φ ih =>
      constructor
      · intro hForce
        by_contra hNotMem
        rcases HasCanonicalNegImpExtensions.not_counterexample (σ := σ) (w := w) (φ := φ) hNotMem with
          ⟨v, hwv, hφMem⟩
        have hφForce : Forces (canonicalModel (σ := σ)) idVarValuation v φ :=
          (ih (w := v)).2 hφMem
        exact hForce v hwv hφForce
      · intro hNotMem v hwv hφForce
        have hNotMemV : (.not φ : Formula σ) ∈ v.carrier := hwv hNotMem
        have hφMemV : φ ∈ v.carrier := (ih (w := v)).1 hφForce
        have hBotDer : Derivable (σ := σ) v.carrier (.bot : Formula σ) := by
          refine ⟨[.not φ, φ], ?_, ?_⟩
          · intro t ht
            simp at ht
            rcases ht with rfl | rfl
            · exact hNotMemV
            · exact hφMemV
          ·
            have h1 : Derives (σ := σ) [.not φ, φ] (.not φ) := Derives.hyp (by simp)
            have h2 : Derives (σ := σ) [.not φ, φ] φ := Derives.hyp (by simp)
            exact Derives.notE h1 h2
        exact v.consistent hBotDer
  | and φ χ ihφ ihχ =>
      constructor
      · intro hForce
        have hφMem : φ ∈ w.carrier := (ihφ (w := w)).1 hForce.1
        have hχMem : χ ∈ w.carrier := (ihχ (w := w)).1 hForce.2
        have hDer : Derivable (σ := σ) w.carrier (.and φ χ) := by
          refine ⟨[φ, χ], ?_, ?_⟩
          · intro t ht
            simp at ht
            rcases ht with rfl | rfl
            · exact hφMem
            · exact hχMem
          ·
            have hφ' : Derives (σ := σ) [φ, χ] φ := Derives.hyp (by simp)
            have hχ' : Derives (σ := σ) [φ, χ] χ := Derives.hyp (by simp)
            exact Derives.andI hφ' hχ'
        exact w.closed _ hDer
      · intro hAndMem
        have hφMem : φ ∈ w.carrier := by
          rcases derivable_of_mem (σ := σ) (T := w.carrier) hAndMem with ⟨Γ, hΓ, hDer⟩
          exact w.closed _ ⟨Γ, hΓ, Derives.andEL hDer⟩
        have hχMem : χ ∈ w.carrier := by
          rcases derivable_of_mem (σ := σ) (T := w.carrier) hAndMem with ⟨Γ, hΓ, hDer⟩
          exact w.closed _ ⟨Γ, hΓ, Derives.andER hDer⟩
        exact And.intro ((ihφ (w := w)).2 hφMem) ((ihχ (w := w)).2 hχMem)
  | or φ χ ihφ ihχ =>
      constructor
      · intro hForce
        cases hForce with
        | inl hφForce =>
            have hφMem : φ ∈ w.carrier := (ihφ (w := w)).1 hφForce
            have hDer : Derivable (σ := σ) w.carrier (.or φ χ) := by
              refine ⟨[φ], ?_, ?_⟩
              · intro t ht
                simp at ht
                subst ht
                exact hφMem
              ·
                have hφ' : Derives (σ := σ) [φ] φ := Derives.hyp (by simp)
                exact Derives.orIL hφ'
            exact w.closed _ hDer
        | inr hχForce =>
            have hχMem : χ ∈ w.carrier := (ihχ (w := w)).1 hχForce
            have hDer : Derivable (σ := σ) w.carrier (.or φ χ) := by
              refine ⟨[χ], ?_, ?_⟩
              · intro t ht
                simp at ht
                subst ht
                exact hχMem
              ·
                have hχ' : Derives (σ := σ) [χ] χ := Derives.hyp (by simp)
                exact Derives.orIR hχ'
            exact w.closed _ hDer
      · intro hOrMem
        rcases w.prime φ χ hOrMem with hφMem | hχMem
        · exact Or.inl ((ihφ (w := w)).2 hφMem)
        · exact Or.inr ((ihχ (w := w)).2 hχMem)
  | imp φ χ ihφ ihχ =>
      constructor
      · intro hForce
        by_contra hImpMem
        rcases HasCanonicalNegImpExtensions.imp_counterexample (σ := σ) (w := w)
            (φ := φ) (ψ := χ) hImpMem with ⟨v, hwv, hφMem, hχNotMem⟩
        have hφForce : Forces (canonicalModel (σ := σ)) idVarValuation v φ :=
          (ihφ (w := v)).2 hφMem
        have hχForce : Forces (canonicalModel (σ := σ)) idVarValuation v χ :=
          hForce v hwv hφForce
        exact hχNotMem ((ihχ (w := v)).1 hχForce)
      · intro hImpMem v hwv hφForce
        have hImpMemV : (.imp φ χ : Formula σ) ∈ v.carrier := hwv hImpMem
        have hφMemV : φ ∈ v.carrier := (ihφ (w := v)).1 hφForce
        have hχDer : Derivable (σ := σ) v.carrier χ := by
          refine ⟨[.imp φ χ, φ], ?_, ?_⟩
          · intro t ht
            simp at ht
            rcases ht with rfl | rfl
            · exact hImpMemV
            · exact hφMemV
          ·
            have h1 : Derives (σ := σ) [.imp φ χ, φ] (.imp φ χ) := Derives.hyp (by simp)
            have h2 : Derives (σ := σ) [.imp φ χ, φ] φ := Derives.hyp (by simp)
            exact Derives.impE h1 h2
        have hχMemV : χ ∈ v.carrier := v.closed _ hχDer
        exact (ihχ (w := v)).2 hχMemV
  | sigma x φ ih =>
      exact HasCanonicalQuantifierTruth.sigma_forces_iff_mem (σ := σ) w x φ
  | pi x φ ih =>
      exact HasCanonicalQuantifierTruth.pi_forces_iff_mem (σ := σ) w x φ

instance (priority := 100)
    hasTruthLemma_of_obligations
    [HasCanonicalNegImpExtensions (σ := σ)]
    [HasCanonicalQuantifierTruth (σ := σ)] :
    HasTruthLemma (σ := σ) where
  truth_iff_mem := truth_iff_mem_of_obligations (σ := σ)

/--
If the full canonical truth lemma is available, the neg/imp extension obligations follow
definitionally from Kripke forcing clauses.
-/
instance (priority := 100)
    hasCanonicalNegImpExtensions_of_truthLemma
    [HasTruthLemma (σ := σ)] :
    HasCanonicalNegImpExtensions (σ := σ) where
  not_counterexample := by
    intro w φ hNotMem
    have hNotForce : ¬ Forces (canonicalModel (σ := σ)) idVarValuation w (.not φ) := by
      intro hForce
      exact hNotMem ((HasTruthLemma.truth_iff_mem (σ := σ) w (.not φ)).1 hForce)
    have hWitness : ∃ v : W (σ := σ), w ≤ v ∧ Forces (canonicalModel (σ := σ)) idVarValuation v φ := by
      by_contra hNo
      apply hNotForce
      intro v hwv hφForce
      exact hNo ⟨v, hwv, hφForce⟩
    rcases hWitness with ⟨v, hwv, hφForce⟩
    refine ⟨v, hwv, ?_⟩
    exact (HasTruthLemma.truth_iff_mem (σ := σ) v φ).1 hφForce
  imp_counterexample := by
    intro w φ ψ hImpMem
    have hImpNotForce : ¬ Forces (canonicalModel (σ := σ)) idVarValuation w (.imp φ ψ) := by
      intro hForce
      exact hImpMem ((HasTruthLemma.truth_iff_mem (σ := σ) w (.imp φ ψ)).1 hForce)
    have hWitness :
        ∃ v : W (σ := σ), w ≤ v ∧
          Forces (canonicalModel (σ := σ)) idVarValuation v φ ∧
          ¬ Forces (canonicalModel (σ := σ)) idVarValuation v ψ := by
      by_contra hNo
      apply hImpNotForce
      intro v hwv hφForce
      by_cases hψForce : Forces (canonicalModel (σ := σ)) idVarValuation v ψ
      · exact hψForce
      · exact False.elim (hNo ⟨v, hwv, hφForce, hψForce⟩)
    rcases hWitness with ⟨v, hwv, hφForce, hψNotForce⟩
    refine ⟨v, hwv, ?_, ?_⟩
    · exact (HasTruthLemma.truth_iff_mem (σ := σ) v φ).1 hφForce
    · intro hψMem
      exact hψNotForce ((HasTruthLemma.truth_iff_mem (σ := σ) v ψ).2 hψMem)

/--
If the full canonical truth lemma is available, quantifier truth obligations are immediate.
-/
instance (priority := 100)
    hasCanonicalQuantifierTruth_of_truthLemma
    [HasTruthLemma (σ := σ)] :
    HasCanonicalQuantifierTruth (σ := σ) where
  sigma_forces_iff_mem := by
    intro w x φ
    exact HasTruthLemma.truth_iff_mem (σ := σ) w (.sigma x φ)
  pi_forces_iff_mem := by
    intro w x φ
    exact HasTruthLemma.truth_iff_mem (σ := σ) w (.pi x φ)

/--
If the full canonical truth lemma is available, `pi`-generalization follows semantically:
instance-membership at `w` lifts to all extensions by monotonicity, then forcing of `pi` yields
membership via truth.
-/
instance (priority := 100)
    hasCanonicalPiGeneralization_of_truthLemma
    [HasTruthLemma (σ := σ)] :
    HasCanonicalPiGeneralization (σ := σ) where
  pi_generalize := by
    intro w x φ hAllInst
    have hPiForce :
        Forces (canonicalModel (σ := σ)) idVarValuation w (.pi x φ) := by
      intro v hwv a
      have hInstMemV :
          Syntax.substFormula (σ := σ) x (.var a) φ ∈ v.carrier :=
        hwv (hAllInst a)
      have hSubstForce :
          Forces (canonicalModel (σ := σ)) idVarValuation v
            (Syntax.substFormula (σ := σ) x (.var a) φ) :=
        (HasTruthLemma.truth_iff_mem
          (σ := σ) (w := v)
          (ψ := Syntax.substFormula (σ := σ) x (.var a) φ)).2 hInstMemV
      exact (KripkeFO.forces_substFormula_var
        (σ := σ)
        (M := canonicalModel (σ := σ))
        (ρ := idVarValuation)
        (w := v)
        x a φ).1 hSubstForce
    exact (HasTruthLemma.truth_iff_mem (σ := σ) (w := w) (ψ := .pi x φ)).1 hPiForce

instance (priority := 100)
    hasCanonicalTruthBySize_of_truthLemma
    [HasTruthLemma (σ := σ)] :
    HasCanonicalTruthBySize (σ := σ) where
  truth_lt := by
    intro _n w ψ _hlt
    exact HasTruthLemma.truth_iff_mem (σ := σ) w ψ

instance (priority := 99)
    hasTruthLemma_of_truthBySize
    [HasCanonicalTruthBySize (σ := σ)] :
    HasTruthLemma (σ := σ) where
  truth_iff_mem := by
    intro w ψ
    exact HasCanonicalTruthBySize.truth_lt
      (σ := σ) (n := Syntax.fSize (σ := σ) ψ + 1) (w := w) (ψ := ψ)
      (Nat.lt_succ_self _)

end InternalFO

/--
Internal FO completeness interface: provide canonical countermodels for non-derivable sequents.

This names the exact internal artifact needed to close the remaining FO completeness gap:
canonical countermodel construction for non-derivable sequents.
-/
class HasInternalCountermodel (σ : Type) : Prop where
  countermodel :
    ∀ {Γ : List (Formula σ)} {φ : Formula σ},
      ¬ Derives (σ := σ) Γ φ →
        ∃ w : InternalFO.W (σ := σ),
          (∀ ψ ∈ Γ,
            Forces (InternalFO.canonicalModel (σ := σ)) InternalFO.idVarValuation w ψ) ∧
          ¬ Forces (InternalFO.canonicalModel (σ := σ)) InternalFO.idVarValuation w φ

instance (priority := 100)
    hasInternalCountermodel_of_extension_truth
    [InternalFO.HasExtensionConstruction (σ := σ)]
    [InternalFO.HasTruthLemma (σ := σ)] :
    HasInternalCountermodel σ where
  countermodel := by
    intro Γ φ hNotDer
    exact InternalFO.countermodel_of_extension_and_truth (σ := σ)
      (Γ := Γ) (φ := φ)
      (InternalFO.HasExtensionConstruction.extend_avoid (σ := σ))
      (InternalFO.HasTruthLemma.truth_iff_mem (σ := σ))
      hNotDer

/-- Completeness obtained from the explicit internal countermodel artifact. -/
theorem completeness_from_internal_countermodel [HasInternalCountermodel σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails (σ := σ) Γ φ → Derives (σ := σ) Γ φ :=
  InternalFO.completeness_from_countermodel (σ := σ) HasInternalCountermodel.countermodel

/--
Sentence-sequent countermodel interface.

This isolates the sentence-focused fallback route: premises are closed formulas, while the
conclusion can still be open at this stage.
-/
class HasSentenceCountermodel (σ : Type) : Prop where
  countermodel :
    ∀ {Γ : List (Formula σ)} {φ : Formula σ},
      (∀ ψ, ψ ∈ Γ → Syntax.fvFormula (σ := σ) ψ = ∅) →
      ¬ Derives (σ := σ) Γ φ →
        ∃ w : InternalFO.W (σ := σ),
          (∀ ψ ∈ Γ,
            Forces (InternalFO.canonicalModel (σ := σ)) InternalFO.idVarValuation w ψ) ∧
          ¬ Forces (InternalFO.canonicalModel (σ := σ)) InternalFO.idVarValuation w φ

instance (priority := 100)
    hasSentenceCountermodel_of_internal
    [HasInternalCountermodel σ] :
    HasSentenceCountermodel σ where
  countermodel := by
    intro Γ φ _hΓClosed hNotDer
    exact HasInternalCountermodel.countermodel (σ := σ) hNotDer

/--
Sentence-sequent countermodel interface with a closed goal and sentence-world witness.

This captures the fully internal sentence route currently available from maximal
sentence-family construction and sentence truth obligations.
-/
class HasSentenceCountermodelClosedGoal (σ : Type) : Prop where
  countermodel :
    ∀ {Γ : List (Formula σ)} {φ : Formula σ},
      (∀ ψ, ψ ∈ Γ → Syntax.fvFormula (σ := σ) ψ = ∅) →
      Syntax.fvFormula (σ := σ) φ = ∅ →
      ¬ Derives (σ := σ) Γ φ →
        ∃ w : InternalFO.SentenceWorld σ,
          (∀ ψ ∈ Γ,
            Forces (InternalFO.sentenceCanonicalModel (σ := σ))
              InternalFO.sentenceIdVarValuation w ψ) ∧
          ¬ Forces (InternalFO.sentenceCanonicalModel (σ := σ))
              InternalFO.sentenceIdVarValuation w φ

/--
Build closed-goal sentence countermodels from the internal sentence-route obligations:
- open weakening for list-derivation transport,
- sentence neg/imp extension obligations,
- sentence quantifier truth obligations.
-/
theorem hasSentenceCountermodelClosedGoal_of_sentence_obligations
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasSentenceClosedDeriv (σ := σ)]
    [InternalFO.HasSentenceNegImpExtensions (σ := σ)]
    [InternalFO.HasSentenceQuantifierTruth (σ := σ)] :
    HasSentenceCountermodelClosedGoal σ where
  countermodel := by
    intro Γ φ hΓClosed hφClosed hNotDer
    rcases InternalFO.Lindenbaum.exists_maximal_sentence_of_notDerives
      (σ := σ)
      (hWeak := InternalFO.HasOpenWeakening.weaken (σ := σ))
      (Γ := Γ) (χ := φ)
      hΓClosed hNotDer with
      ⟨M, hSM, hMax⟩
    have hMF :
        M ∈ InternalFO.Lindenbaum.SentenceFamily (σ := σ) {ψ | ψ ∈ Γ} φ :=
      hMax.prop
    let w : InternalFO.SentenceWorld σ :=
      InternalFO.SentenceWorld.ofMaximalSentence
        (σ := σ)
        (hWeak := InternalFO.HasOpenWeakening.weaken (σ := σ))
        (S := {ψ | ψ ∈ Γ}) (χ := φ) (M := M) hMF hMax
    refine ⟨w, ?_, ?_⟩
    · intro ψ hψ
      have hψMem : ψ ∈ w.carrier := hSM (by simpa using hψ)
      exact (InternalFO.sentence_truth_iff_mem_closed_of_obligations
        (σ := σ) (w := w) (ψ := ψ) (hΓClosed ψ hψ)).2 hψMem
    ·
      have hφNotMem : φ ∉ w.carrier :=
        InternalFO.Lindenbaum.goal_not_mem_of_sentenceFamily (σ := σ) hMF
      intro hForce
      exact hφNotMem ((InternalFO.sentence_truth_iff_mem_closed_of_obligations
        (σ := σ) (w := w) (ψ := φ) hφClosed).1 hForce)

/--
Closed-goal sentence-sequent completeness from the sentence-world countermodel interface.
-/
theorem sentence_completeness_closedGoal_from_countermodel
    [HasSentenceCountermodelClosedGoal σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓClosed : ∀ ψ, ψ ∈ Γ → Syntax.fvFormula (σ := σ) ψ = ∅)
    (hφClosed : Syntax.fvFormula (σ := σ) φ = ∅) :
    Entails (σ := σ) Γ φ → Derives (σ := σ) Γ φ := by
  intro hEnt
  by_contra hNotDer
  rcases HasSentenceCountermodelClosedGoal.countermodel (σ := σ)
    (Γ := Γ) (φ := φ) hΓClosed hφClosed hNotDer with
    ⟨w, hwΓ, hNotφ⟩
  exact hNotφ (hEnt
    (W := InternalFO.SentenceWorld (σ := σ))
    (D := Var)
    (M := InternalFO.sentenceCanonicalModel (σ := σ))
    (ρ := InternalFO.sentenceIdVarValuation)
    (w := w)
    hwΓ)

/--
Closed-goal sentence completeness after universally closing assumptions.

This theorem is useful when the premise context is open: we can transport entailment to
`closeContext Γ`, discharge completeness on the closed context, and continue from there.
-/
theorem sentence_completeness_closedGoal_on_closeContext_from_countermodel
    [HasSentenceCountermodelClosedGoal σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hφClosed : Syntax.fvFormula (σ := σ) φ = ∅) :
    Entails (σ := σ) Γ φ ->
      Derives (σ := σ) (Quantifiers.closeContext (σ := σ) Γ) φ := by
  intro hEnt
  have hEntClosedCtx :
      Entails (σ := σ) (Quantifiers.closeContext (σ := σ) Γ) φ :=
    Quantifiers.KripkeFO.entails_of_entails_closeContext
      (σ := σ) (Γ := Γ) (φ := φ) hEnt
  have hClosedCtx :
      ∀ ψ, ψ ∈ Quantifiers.closeContext (σ := σ) Γ ->
        Syntax.fvFormula (σ := σ) ψ = ∅ := by
    intro ψ hψ
    rcases List.mem_map.mp hψ with ⟨θ, _hθ, hEq⟩
    subst hEq
    exact Quantifiers.fv_closeFormula_eq_empty (σ := σ) θ
  exact sentence_completeness_closedGoal_from_countermodel
    (σ := σ)
    (Γ := Quantifiers.closeContext (σ := σ) Γ)
    (φ := φ)
    hClosedCtx
    hφClosed
    hEntClosedCtx

/--
Canonical closed-sequent completeness projection.

From any entailment `Γ ⊨ φ`, derive the fully closed target
`closeContext Γ ⊢ closeFormula φ`.
-/
theorem sentence_completeness_closeContext_closeFormula_from_countermodel
    [HasSentenceCountermodelClosedGoal σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails (σ := σ) Γ φ ->
      Derives (σ := σ)
        (Quantifiers.closeContext (σ := σ) Γ)
        (Quantifiers.closeFormula (σ := σ) φ) := by
  intro hEnt
  have hEntClosed :
      Entails (σ := σ)
        (Quantifiers.closeContext (σ := σ) Γ)
        (Quantifiers.closeFormula (σ := σ) φ) :=
    Quantifiers.KripkeFO.entails_closeContext_closeFormula_of_entails
      (σ := σ) (Γ := Γ) (φ := φ) hEnt
  have hClosedCtx :
      ∀ ψ, ψ ∈ Quantifiers.closeContext (σ := σ) Γ ->
        Syntax.fvFormula (σ := σ) ψ = ∅ := by
    intro ψ hψ
    rcases List.mem_map.mp hψ with ⟨θ, _hθ, hEq⟩
    subst hEq
    exact Quantifiers.fv_closeFormula_eq_empty (σ := σ) θ
  exact sentence_completeness_closedGoal_from_countermodel
    (σ := σ)
    (Γ := Quantifiers.closeContext (σ := σ) Γ)
    (φ := Quantifiers.closeFormula (σ := σ) φ)
    hClosedCtx
    (Quantifiers.fv_closeFormula_eq_empty (σ := σ) φ)
    hEntClosed

/--
Canonical closed-context completeness with original goal.

This follows by proving `closeFormula φ` first and then eliminating universal closure.
-/
theorem sentence_completeness_closeContext_from_countermodel
    [HasSentenceCountermodelClosedGoal σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails (σ := σ) Γ φ ->
      Derives (σ := σ) (Quantifiers.closeContext (σ := σ) Γ) φ := by
  intro hEnt
  have hDerClosed :
      Derives (σ := σ)
        (Quantifiers.closeContext (σ := σ) Γ)
        (Quantifiers.closeFormula (σ := σ) φ) :=
    sentence_completeness_closeContext_closeFormula_from_countermodel
      (σ := σ) (Γ := Γ) (φ := φ) hEnt
  exact Quantifiers.derives_of_closeFormula
    (σ := σ)
    (Γ := Quantifiers.closeContext (σ := σ) Γ)
    (φ := φ)
    hDerClosed

/--
Closed-premise sentence completeness from the closed-goal sentence countermodel interface.
-/
theorem sentence_completeness_closedPremises_from_closedGoal_countermodel
    [HasSentenceCountermodelClosedGoal σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓClosed : ∀ ψ, ψ ∈ Γ → Syntax.fvFormula (σ := σ) ψ = ∅) :
    Entails (σ := σ) Γ φ -> Derives (σ := σ) Γ φ := by
  intro hEnt
  have hDerCloseCtx :
      Derives (σ := σ) (Quantifiers.closeContext (σ := σ) Γ) φ :=
    sentence_completeness_closeContext_from_countermodel
      (σ := σ) (Γ := Γ) (φ := φ) hEnt
  have hCtxEq :
      Quantifiers.closeContext (σ := σ) Γ = Γ :=
    Quantifiers.closeContext_eq_self_of_closed (σ := σ) Γ hΓClosed
  simpa [hCtxEq] using hDerCloseCtx

/--
Closed-premise sentence sound+completeness from the closed-goal sentence countermodel interface.
-/
theorem sentence_sound_complete_closedPremises_from_closedGoal_countermodel
    [HasSentenceCountermodelClosedGoal σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓClosed : ∀ ψ, ψ ∈ Γ → Syntax.fvFormula (σ := σ) ψ = ∅) :
    Derives (σ := σ) Γ φ ↔ Entails (σ := σ) Γ φ := by
  constructor
  · intro hDer
    exact KripkeFO.soundness (σ := σ) hDer
  · intro hEnt
    exact sentence_completeness_closedPremises_from_closedGoal_countermodel
      (σ := σ) (Γ := Γ) (φ := φ) hΓClosed hEnt

/--
Closed-premise sentence completeness directly from the sentence-obligation bundle.
-/
theorem sentence_completeness_closedPremises_from_sentence_obligations
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasSentenceClosedDeriv (σ := σ)]
    [InternalFO.HasSentenceNegImpExtensions (σ := σ)]
    [InternalFO.HasSentenceQuantifierTruth (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓClosed : ∀ ψ, ψ ∈ Γ → Syntax.fvFormula (σ := σ) ψ = ∅) :
    Entails (σ := σ) Γ φ -> Derives (σ := σ) Γ φ := by
  letI : HasSentenceCountermodelClosedGoal σ :=
    hasSentenceCountermodelClosedGoal_of_sentence_obligations (σ := σ)
  exact sentence_completeness_closedPremises_from_closedGoal_countermodel
    (σ := σ) (Γ := Γ) (φ := φ) hΓClosed

/--
Closed-premise sentence sound+completeness directly from the sentence-obligation bundle.
-/
theorem sentence_sound_complete_closedPremises_from_sentence_obligations
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasSentenceClosedDeriv (σ := σ)]
    [InternalFO.HasSentenceNegImpExtensions (σ := σ)]
    [InternalFO.HasSentenceQuantifierTruth (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓClosed : ∀ ψ, ψ ∈ Γ → Syntax.fvFormula (σ := σ) ψ = ∅) :
    Derives (σ := σ) Γ φ ↔ Entails (σ := σ) Γ φ := by
  letI : HasSentenceCountermodelClosedGoal σ :=
    hasSentenceCountermodelClosedGoal_of_sentence_obligations (σ := σ)
  exact sentence_sound_complete_closedPremises_from_closedGoal_countermodel
    (σ := σ) (Γ := Γ) (φ := φ) hΓClosed

/--
Closed-goal sentence-sequent sound+completeness from the sentence-world countermodel interface.
-/
theorem sentence_sound_complete_closedGoal_from_countermodel
    [HasSentenceCountermodelClosedGoal σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓClosed : ∀ ψ, ψ ∈ Γ → Syntax.fvFormula (σ := σ) ψ = ∅)
    (hφClosed : Syntax.fvFormula (σ := σ) φ = ∅) :
    Derives (σ := σ) Γ φ ↔ Entails (σ := σ) Γ φ := by
  constructor
  · intro hDer
    exact KripkeFO.soundness (σ := σ) hDer
  · intro hEnt
    exact sentence_completeness_closedGoal_from_countermodel
      (σ := σ) (Γ := Γ) (φ := φ) hΓClosed hφClosed hEnt

/--
Full-sequent completeness from the sentence countermodel interface via implication-chain encoding.

This route avoids the open-family fresh-cons extractor by reducing `Γ ⊨ φ` to the closed-goal
sentence route on `[] ⊨ impChain Γ φ`, then decoding the implication chain back to `Γ ⊢ φ`.
-/
theorem completeness_from_sentence_countermodel_impChain
    [HasSentenceCountermodelClosedGoal σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails (σ := σ) Γ φ → Derives (σ := σ) Γ φ := by
  intro hEnt
  have hEntChain :
      Entails (σ := σ) [] (Quantifiers.impChain (σ := σ) Γ φ) :=
    Quantifiers.KripkeFO.entails_nil_impChain_of_entails
      (σ := σ) (Γ := Γ) (φ := φ) hEnt
  have hDerChainClose :
      Derives (σ := σ)
        (Quantifiers.closeContext (σ := σ) [])
        (Quantifiers.impChain (σ := σ) Γ φ) :=
    sentence_completeness_closeContext_from_countermodel
      (σ := σ)
      (Γ := [])
      (φ := Quantifiers.impChain (σ := σ) Γ φ)
      hEntChain
  have hDerChain :
      Derives (σ := σ) [] (Quantifiers.impChain (σ := σ) Γ φ) := by
    simpa [Quantifiers.closeContext] using hDerChainClose
  exact Quantifiers.derives_of_impChain_nil
    (σ := σ) (Γ := Γ) (φ := φ) hDerChain

/-- Full-sequent sound+completeness from the implication-chain sentence route. -/
theorem sound_complete_from_sentence_countermodel_impChain
    [HasSentenceCountermodelClosedGoal σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Derives (σ := σ) Γ φ ↔ Entails (σ := σ) Γ φ := by
  constructor
  · intro hDer
    exact KripkeFO.soundness (σ := σ) hDer
  · intro hEnt
    exact completeness_from_sentence_countermodel_impChain
      (σ := σ) (Γ := Γ) (φ := φ) hEnt

/-- Sentence-sequent completeness from the sentence countermodel interface. -/
theorem sentence_completeness_from_countermodel [HasSentenceCountermodel σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓClosed : ∀ ψ, ψ ∈ Γ → Syntax.fvFormula (σ := σ) ψ = ∅) :
    Entails (σ := σ) Γ φ → Derives (σ := σ) Γ φ := by
  intro hEnt
  by_contra hNotDer
  rcases HasSentenceCountermodel.countermodel (σ := σ)
    (Γ := Γ) (φ := φ) hΓClosed hNotDer with
    ⟨w, hwΓ, hNotφ⟩
  exact hNotφ (hEnt (W := InternalFO.W (σ := σ))
    (D := Var)
    (M := InternalFO.canonicalModel (σ := σ))
    (ρ := InternalFO.idVarValuation)
    (w := w)
    hwΓ)

/-- Sentence-sequent sound+completeness from the sentence countermodel interface. -/
theorem sentence_sound_complete_from_countermodel [HasSentenceCountermodel σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓClosed : ∀ ψ, ψ ∈ Γ → Syntax.fvFormula (σ := σ) ψ = ∅) :
    Derives (σ := σ) Γ φ ↔ Entails (σ := σ) Γ φ := by
  constructor
  · intro hDer
    exact KripkeFO.soundness (σ := σ) hDer
  · intro hEnt
    exact sentence_completeness_from_countermodel (σ := σ)
      (Γ := Γ) (φ := φ) hΓClosed hEnt

/--
Full-sequent completeness from the sentence-obligation bundle, via implication-chain reduction.
-/
theorem completeness_from_sentence_obligations_impChain
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasSentenceClosedDeriv (σ := σ)]
    [InternalFO.HasSentenceNegImpExtensions (σ := σ)]
    [InternalFO.HasSentenceQuantifierTruth (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails (σ := σ) Γ φ → Derives (σ := σ) Γ φ := by
  letI : HasSentenceCountermodelClosedGoal σ :=
    hasSentenceCountermodelClosedGoal_of_sentence_obligations (σ := σ)
  exact completeness_from_sentence_countermodel_impChain
    (σ := σ) (Γ := Γ) (φ := φ)

/--
Full-sequent sound+completeness from the sentence-obligation bundle,
via implication-chain reduction.
-/
theorem sound_complete_from_sentence_obligations_impChain
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasSentenceClosedDeriv (σ := σ)]
    [InternalFO.HasSentenceNegImpExtensions (σ := σ)]
    [InternalFO.HasSentenceQuantifierTruth (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Derives (σ := σ) Γ φ ↔ Entails (σ := σ) Γ φ := by
  letI : HasSentenceCountermodelClosedGoal σ :=
    hasSentenceCountermodelClosedGoal_of_sentence_obligations (σ := σ)
  exact sound_complete_from_sentence_countermodel_impChain
    (σ := σ) (Γ := Γ) (φ := φ)

instance (priority := 96)
    hasSequentFamilyBase_of_internalCountermodel
    [HasInternalCountermodel σ] :
    InternalFO.HasSequentFamilyBase (σ := σ) where
  base_consistent := by
    intro Γ φ hNotDer hInconsistent
    rcases hInconsistent with ⟨Δ, hΔS, hDerBot⟩
    have hSub : Δ ⊆ Γ := by
      intro ψ hψ
      exact hΔS ψ hψ
    have hEntΔBot : Entails (σ := σ) Δ (.bot : Formula σ) :=
      KripkeFO.soundness (σ := σ) hDerBot
    have hEntΓBot : Entails (σ := σ) Γ (.bot : Formula σ) :=
      InternalFO.entails_mono_of_subset
        (σ := σ) (Γ := Γ) (Δ := Δ) (φ := (.bot : Formula σ)) hSub hEntΔBot
    have hDerΓBot : Derives (σ := σ) Γ (.bot : Formula σ) :=
      completeness_from_internal_countermodel (σ := σ) hEntΓBot
    exact hNotDer (Derives.botE hDerΓBot)
  base_notDerivable := by
    intro Γ φ hNotDer hDerivable
    rcases hDerivable with ⟨Δ, hΔS, hDerΔ⟩
    have hSub : Δ ⊆ Γ := by
      intro ψ hψ
      exact hΔS ψ hψ
    have hEntΔ : Entails (σ := σ) Δ φ :=
      KripkeFO.soundness (σ := σ) hDerΔ
    have hEntΓ : Entails (σ := σ) Γ φ :=
      InternalFO.entails_mono_of_subset (σ := σ) (Γ := Γ) (Δ := Δ) (φ := φ) hSub hEntΔ
    exact hNotDer (completeness_from_internal_countermodel (σ := σ) hEntΓ)

instance (priority := 96)
    hasSaturatedPromotion_of_openWeakening_henkin
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasHenkinSigmaPromotion (σ := σ)] :
    InternalFO.HasSaturatedPromotion (σ := σ) where
  of_maximal := by
    intro S χ M hMF hMax
    have hClosed :
        ∀ θ : Formula σ, InternalFO.Derivable (σ := σ) M θ → θ ∈ M :=
      InternalFO.Lindenbaum.closed_of_maximal_via_complete
        (σ := σ)
        (hWeak := InternalFO.HasOpenWeakening.weaken (σ := σ))
        (hMF := hMF) (hMax := hMax)
    have hPrime :
        ∀ φ ψ : Formula σ, (.or φ ψ : Formula σ) ∈ M → φ ∈ M ∨ ψ ∈ M :=
      InternalFO.Lindenbaum.prime_of_maximal_via_complete
        (σ := σ)
        (hWeak := InternalFO.HasOpenWeakening.weaken (σ := σ))
        (hMF := hMF) (hMax := hMax)
    refine ⟨{
      carrier := M
      consistent := hMF.1
      closed := hClosed
      prime := hPrime
      henkinSigma := ?_
      henkinPi := ?_
    }, hMF.2.1, ?_⟩
    · intro x φ hSigmaMem
      exact InternalFO.HasHenkinSigmaPromotion.sigma_witness_of_maximal
        (σ := σ) (S := S) (χ := χ) (M := M) hMF hMax hSigmaMem
    · intro x φ hPiMem a haBound
      have hDer : InternalFO.Derivable (σ := σ) M
          (Syntax.substFormula (σ := σ) x (.var a) φ) := by
        refine InternalFO.derivable_of_derives (σ := σ)
          (T := M) (Γ := [.pi x φ]) (φ := Syntax.substFormula (σ := σ) x (.var a) φ) ?_ ?_
        · intro ψ hψ
          simp at hψ
          subst hψ
          exact hPiMem
        ·
          have hHyp : Derives (σ := σ) [.pi x φ] (.pi x φ) :=
            Derives.hyp (by simp)
          exact Derives.piE hHyp
      exact hClosed _ hDer
    · intro hχMem
      exact hMF.2.2 (InternalFO.derivable_of_mem (σ := σ) (T := M) hχMem)

instance (priority := 95)
    hasWitnessInsertionFamily_of_openWeakening_freshCons
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasFreshSigmaConsFromInsertOnFamily (σ := σ)] :
    InternalFO.HasWitnessInsertionFamily (σ := σ) :=
  InternalFO.hasWitnessInsertionFamily_of_complete_and_freshCons (σ := σ)
    (hWeak := InternalFO.HasOpenWeakening.weaken (σ := σ))

/--
Build witness insertion from open weakening plus the focused tail-fresh extraction obligation.
-/
instance (priority := 95)
    hasWitnessInsertionFamily_of_openWeakening_tailFresh
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasTailFreshSigmaConsOnFamily (σ := σ)] :
    InternalFO.HasWitnessInsertionFamily (σ := σ) := by
  letI : InternalFO.HasFreshSigmaConsFromInsertOnFamily (σ := σ) :=
    InternalFO.hasFreshSigmaConsFromInsertOnFamily_of_tailFresh (σ := σ)
  infer_instance

/--
Build witness insertion from open weakening plus implication extraction in `DerivesEFresh`.

This uses the equivalence
`HasFreshDerivesEFreshImpOnFamily <-> HasFreshSigmaConsFromInsertOnFamily`.
-/
instance (priority := 95)
    hasWitnessInsertionFamily_of_openWeakening_derivesEFreshImp
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasFreshDerivesEFreshImpOnFamily (σ := σ)] :
    InternalFO.HasWitnessInsertionFamily (σ := σ) := by
  letI : InternalFO.HasFreshSigmaConsFromInsertOnFamily (σ := σ) :=
    InternalFO.hasFreshSigmaConsFromInsertOnFamily_of_derivesEFreshImp (σ := σ)
  infer_instance

instance (priority := 94)
    hasCanonicalNegImpExtensions_of_openWeakening_sentenceFamilyClosure
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasSentenceFamilyClosure (σ := σ)] :
    InternalFO.HasCanonicalNegImpExtensions (σ := σ) := by
  letI : InternalFO.HasSaturatedPromotion (σ := σ) := by
    infer_instance
  exact InternalFO.hasCanonicalNegImpExtensions_of_openWeakening_saturatedPromotion (σ := σ)

-- This route is intentionally not used by default typeclass search.
attribute [-instance] hasCanonicalNegImpExtensions_of_openWeakening_sentenceFamilyClosure

instance (priority := 94)
    hasCanonicalTruthBySize_of_openWeakening_sentenceFamilyClosure
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasSentenceFamilyClosure (σ := σ)] :
    InternalFO.HasCanonicalTruthBySize (σ := σ) := by
  letI : InternalFO.HasCanonicalPiGeneralization (σ := σ) := by
    infer_instance
  letI : InternalFO.HasCanonicalNegImpExtensions (σ := σ) := by
    exact hasCanonicalNegImpExtensions_of_openWeakening_sentenceFamilyClosure (σ := σ)
  infer_instance

-- This route is intentionally not used by default typeclass search.
attribute [-instance] hasCanonicalTruthBySize_of_openWeakening_sentenceFamilyClosure

/--
Build extension construction from open weakening plus the focused fresh-cons quantifier obligation.

This is the strongest fully internal route that does not assume theory-closure of maximal members:
`open weakening -> fresh-cons -> witness insertion -> Henkin sigma -> saturated world extension`.
-/
theorem hasExtensionConstruction_of_openWeakening_freshCons
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasFreshSigmaConsFromInsertOnFamily (σ := σ)] :
    InternalFO.HasExtensionConstruction (σ := σ) := by
  letI : InternalFO.HasWitnessInsertionFamily (σ := σ) := by
    infer_instance
  letI : InternalFO.HasHenkinSigmaPromotion (σ := σ) := by
    infer_instance
  letI : InternalFO.HasSaturatedPromotion (σ := σ) := by
    infer_instance
  letI : InternalFO.HasSequentFamilyBase (σ := σ) := by
    infer_instance
  infer_instance

/--
Build extension construction from open weakening plus the focused tail-fresh extraction obligation.
-/
theorem hasExtensionConstruction_of_openWeakening_tailFresh
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasTailFreshSigmaConsOnFamily (σ := σ)] :
    InternalFO.HasExtensionConstruction (σ := σ) := by
  letI : InternalFO.HasFreshSigmaConsFromInsertOnFamily (σ := σ) :=
    InternalFO.hasFreshSigmaConsFromInsertOnFamily_of_tailFresh (σ := σ)
  exact hasExtensionConstruction_of_openWeakening_freshCons (σ := σ)

/--
Build extension construction from open weakening plus implication extraction in `DerivesEFresh`.
-/
theorem hasExtensionConstruction_of_openWeakening_derivesEFreshImp
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasFreshDerivesEFreshImpOnFamily (σ := σ)] :
    InternalFO.HasExtensionConstruction (σ := σ) := by
  letI : InternalFO.HasFreshSigmaConsFromInsertOnFamily (σ := σ) :=
    InternalFO.hasFreshSigmaConsFromInsertOnFamily_of_derivesEFreshImp (σ := σ)
  exact hasExtensionConstruction_of_openWeakening_freshCons (σ := σ)

/--
Build extension construction from open weakening plus a global variable-freshness fact.

This route bypasses source-fresh extraction and uses the stronger witness-insertion assumption:
there is one variable `a` fresh for `χ` and absent from `varsFormula` of every member formula.
-/
theorem hasExtensionConstruction_of_openWeakening_globalVarFresh
    [InternalFO.HasOpenWeakening (σ := σ)]
    (hGlobalVarFresh :
      ∀ {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)},
        M ∈ InternalFO.Lindenbaum.Family (σ := σ) S χ →
        Maximal (· ∈ InternalFO.Lindenbaum.Family (σ := σ) S χ) M →
        ∃ a : Var,
          a ∉ Syntax.fvFormula (σ := σ) χ ∧
          (∀ ψ, ψ ∈ M → a ∉ Syntax.varsFormula (σ := σ) ψ)) :
    InternalFO.HasExtensionConstruction (σ := σ) := by
  letI : InternalFO.HasWitnessInsertionFamily (σ := σ) :=
    InternalFO.hasWitnessInsertionFamily_of_openWeakening_globalVarFresh
      (σ := σ) hGlobalVarFresh
  letI : InternalFO.HasHenkinSigmaPromotion (σ := σ) := by
    infer_instance
  letI : InternalFO.HasSaturatedPromotion (σ := σ) := by
    infer_instance
  letI : InternalFO.HasSequentFamilyBase (σ := σ) := by
    infer_instance
  infer_instance

/--
Build extension construction from open weakening plus finite-support maximal Lindenbaum members.
-/
theorem hasExtensionConstruction_of_openWeakening_finiteSupport
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasFiniteSupportFamily (σ := σ)] :
    InternalFO.HasExtensionConstruction (σ := σ) := by
  letI : InternalFO.HasWitnessInsertionFamily (σ := σ) :=
    InternalFO.hasWitnessInsertionFamily_of_openWeakening_finiteSupport (σ := σ)
  letI : InternalFO.HasHenkinSigmaPromotion (σ := σ) := by
    infer_instance
  letI : InternalFO.HasSaturatedPromotion (σ := σ) := by
    infer_instance
  letI : InternalFO.HasSequentFamilyBase (σ := σ) := by
    infer_instance
  infer_instance

/--
Build extension construction from open weakening plus closed-theory freshness on Lindenbaum members.

This packages the quantifier-promotion chain into a single internal theorem:
`theoryClosed -> fresh-cons -> witness insertion -> Henkin sigma -> saturated world extension`.
-/
theorem hasExtensionConstruction_of_openWeakening_theoryClosed
    [InternalFO.HasOpenWeakening (σ := σ)]
    (hTheoryClosed :
      ∀ {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)},
        M ∈ InternalFO.Lindenbaum.Family (σ := σ) S χ →
        Maximal (· ∈ InternalFO.Lindenbaum.Family (σ := σ) S χ) M →
        ∀ ψ, ψ ∈ M → Syntax.fvFormula (σ := σ) ψ = ∅) :
    InternalFO.HasExtensionConstruction (σ := σ) := by
  letI : InternalFO.HasFreshSigmaConsFromInsertOnFamily (σ := σ) :=
    InternalFO.hasFreshSigmaConsFromInsertOnFamily_of_theoryClosed
      (σ := σ)
      (hWeak := InternalFO.HasOpenWeakening.weaken (σ := σ))
      hTheoryClosed
  letI : InternalFO.HasWitnessInsertionFamily (σ := σ) := by
    infer_instance
  letI : InternalFO.HasHenkinSigmaPromotion (σ := σ) := by
    infer_instance
  letI : InternalFO.HasSaturatedPromotion (σ := σ) := by
    infer_instance
  infer_instance

/--
Build internal countermodels from:
- open weakening,
- closed-theory freshness on Lindenbaum members,
- canonical neg/imp extensions,
- canonical quantifier truth.
-/
theorem hasInternalCountermodel_of_openWeakening_theoryClosed_obligations
    [InternalFO.HasOpenWeakening (σ := σ)]
    (hTheoryClosed :
      ∀ {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)},
        M ∈ InternalFO.Lindenbaum.Family (σ := σ) S χ →
        Maximal (· ∈ InternalFO.Lindenbaum.Family (σ := σ) S χ) M →
        ∀ ψ, ψ ∈ M → Syntax.fvFormula (σ := σ) ψ = ∅)
    [InternalFO.HasCanonicalNegImpExtensions (σ := σ)]
    [InternalFO.HasCanonicalQuantifierTruth (σ := σ)] :
    HasInternalCountermodel σ := by
  letI : InternalFO.HasExtensionConstruction (σ := σ) :=
    hasExtensionConstruction_of_openWeakening_theoryClosed
      (σ := σ) hTheoryClosed
  letI : InternalFO.HasTruthLemma (σ := σ) := by
    infer_instance
  infer_instance

/--
Build internal countermodels from:
- open weakening,
- sentence-family closure on maximal Lindenbaum members,
- canonical neg/imp extensions,
- canonical quantifier truth.
-/
theorem hasInternalCountermodel_of_openWeakening_sentenceFamily_obligations
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasSentenceFamilyClosure (σ := σ)]
    [InternalFO.HasCanonicalNegImpExtensions (σ := σ)]
    [InternalFO.HasCanonicalQuantifierTruth (σ := σ)] :
    HasInternalCountermodel σ := by
  letI : InternalFO.HasExtensionConstruction (σ := σ) :=
    hasExtensionConstruction_of_openWeakening_theoryClosed
      (σ := σ)
      (hTheoryClosed := InternalFO.HasSentenceFamilyClosure.theory_closed (σ := σ))
  letI : InternalFO.HasTruthLemma (σ := σ) := by
    infer_instance
  infer_instance

/--
Build internal countermodels from:
- open weakening,
- focused fresh-cons quantifier obligation on Lindenbaum families,
- canonical neg/imp extensions,
- canonical quantifier truth.
-/
theorem hasInternalCountermodel_of_openWeakening_freshCons_obligations
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasFreshSigmaConsFromInsertOnFamily (σ := σ)]
    [InternalFO.HasCanonicalNegImpExtensions (σ := σ)]
    [InternalFO.HasCanonicalQuantifierTruth (σ := σ)] :
    HasInternalCountermodel σ := by
  letI : InternalFO.HasExtensionConstruction (σ := σ) :=
    hasExtensionConstruction_of_openWeakening_freshCons (σ := σ)
  letI : InternalFO.HasTruthLemma (σ := σ) := by
    infer_instance
  infer_instance

/--
Build internal countermodels from:
- open weakening,
- focused tail-fresh extraction on Lindenbaum families,
- canonical neg/imp extensions,
- canonical quantifier truth.
-/
theorem hasInternalCountermodel_of_openWeakening_tailFresh_obligations
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasTailFreshSigmaConsOnFamily (σ := σ)]
    [InternalFO.HasCanonicalNegImpExtensions (σ := σ)]
    [InternalFO.HasCanonicalQuantifierTruth (σ := σ)] :
    HasInternalCountermodel σ := by
  letI : InternalFO.HasFreshSigmaConsFromInsertOnFamily (σ := σ) :=
    InternalFO.hasFreshSigmaConsFromInsertOnFamily_of_tailFresh (σ := σ)
  exact hasInternalCountermodel_of_openWeakening_freshCons_obligations (σ := σ)

/--
Build internal countermodels from:
- open weakening,
- focused tail-fresh extraction on Lindenbaum families,
- canonical `pi` generalization.
-/
theorem hasInternalCountermodel_of_openWeakening_tailFresh_piGeneralization
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasTailFreshSigmaConsOnFamily (σ := σ)]
    [InternalFO.HasCanonicalPiGeneralization (σ := σ)] :
    HasInternalCountermodel σ := by
  letI : InternalFO.HasFreshSigmaConsFromInsertOnFamily (σ := σ) :=
    InternalFO.hasFreshSigmaConsFromInsertOnFamily_of_tailFresh (σ := σ)
  letI : InternalFO.HasWitnessInsertionFamily (σ := σ) := by
    infer_instance
  letI : InternalFO.HasHenkinSigmaPromotion (σ := σ) := by
    infer_instance
  letI : InternalFO.HasSaturatedPromotion (σ := σ) := by
    infer_instance
  letI : InternalFO.HasCanonicalNegImpExtensions (σ := σ) :=
    InternalFO.hasCanonicalNegImpExtensions_of_openWeakening_saturatedPromotion (σ := σ)
  letI : InternalFO.HasCanonicalQuantifierTruth (σ := σ) := by
    infer_instance
  exact hasInternalCountermodel_of_openWeakening_tailFresh_obligations (σ := σ)

/--
Build internal countermodels from:
- open weakening,
- focused tail-fresh extraction on Lindenbaum families,
- a full canonical truth lemma.
-/
theorem hasInternalCountermodel_of_openWeakening_tailFresh_truthLemma
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasTailFreshSigmaConsOnFamily (σ := σ)]
    [InternalFO.HasTruthLemma (σ := σ)] :
    HasInternalCountermodel σ := by
  letI : InternalFO.HasCanonicalNegImpExtensions (σ := σ) := by
    infer_instance
  letI : InternalFO.HasCanonicalQuantifierTruth (σ := σ) := by
    infer_instance
  exact hasInternalCountermodel_of_openWeakening_tailFresh_obligations (σ := σ)

/--
Build internal countermodels from:
- open weakening,
- focused tail-fresh extraction on Lindenbaum families,
- canonical truth-by-size.
-/
theorem hasInternalCountermodel_of_openWeakening_tailFresh_truthBySize
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasTailFreshSigmaConsOnFamily (σ := σ)]
    [InternalFO.HasCanonicalTruthBySize (σ := σ)] :
    HasInternalCountermodel σ := by
  letI : InternalFO.HasTruthLemma (σ := σ) := by
    infer_instance
  exact hasInternalCountermodel_of_openWeakening_tailFresh_truthLemma (σ := σ)

/--
Build internal countermodels from:
- open weakening,
- focused fresh-cons quantifier obligation on Lindenbaum families,
- canonical quantifier truth.

`HasCanonicalNegImpExtensions` is discharged internally from open-weakening + saturated promotion.
-/
theorem hasInternalCountermodel_of_openWeakening_freshCons_quantifierTruth
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasFreshSigmaConsFromInsertOnFamily (σ := σ)]
    [InternalFO.HasCanonicalQuantifierTruth (σ := σ)] :
    HasInternalCountermodel σ := by
  letI : InternalFO.HasWitnessInsertionFamily (σ := σ) := by
    infer_instance
  letI : InternalFO.HasHenkinSigmaPromotion (σ := σ) := by
    infer_instance
  letI : InternalFO.HasSaturatedPromotion (σ := σ) := by
    infer_instance
  letI : InternalFO.HasCanonicalNegImpExtensions (σ := σ) :=
    InternalFO.hasCanonicalNegImpExtensions_of_openWeakening_saturatedPromotion (σ := σ)
  exact hasInternalCountermodel_of_openWeakening_freshCons_obligations (σ := σ)

/--
Build internal countermodels from:
- open weakening,
- focused fresh-cons quantifier obligation on Lindenbaum families,
- canonical `pi` generalization.

Quantifier truth is now recovered internally from:
`HasCanonicalNegImpExtensions + HasCanonicalPiGeneralization`
via the size-recursive canonical truth artifact.
-/
theorem hasInternalCountermodel_of_openWeakening_freshCons_piGeneralization
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasFreshSigmaConsFromInsertOnFamily (σ := σ)]
    [InternalFO.HasCanonicalPiGeneralization (σ := σ)] :
    HasInternalCountermodel σ := by
  letI : InternalFO.HasWitnessInsertionFamily (σ := σ) := by
    infer_instance
  letI : InternalFO.HasHenkinSigmaPromotion (σ := σ) := by
    infer_instance
  letI : InternalFO.HasSaturatedPromotion (σ := σ) := by
    infer_instance
  letI : InternalFO.HasCanonicalNegImpExtensions (σ := σ) :=
    InternalFO.hasCanonicalNegImpExtensions_of_openWeakening_saturatedPromotion (σ := σ)
  letI : InternalFO.HasCanonicalQuantifierTruth (σ := σ) := by
    infer_instance
  exact hasInternalCountermodel_of_openWeakening_freshCons_obligations (σ := σ)

/--
Build internal countermodels from:
- open weakening,
- focused fresh-cons quantifier obligation on Lindenbaum families,
- a full canonical truth lemma.

This route bypasses explicit canonical neg/imp and quantifier-truth classes when truth is already
available as one internal artifact.
-/
theorem hasInternalCountermodel_of_openWeakening_freshCons_truthLemma
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasFreshSigmaConsFromInsertOnFamily (σ := σ)]
    [InternalFO.HasTruthLemma (σ := σ)] :
    HasInternalCountermodel σ := by
  letI : InternalFO.HasExtensionConstruction (σ := σ) :=
    hasExtensionConstruction_of_openWeakening_freshCons (σ := σ)
  infer_instance

/--
Build internal countermodels from:
- open weakening,
- focused fresh-cons quantifier obligation on Lindenbaum families,
- canonical truth-by-size.

Truth-by-size is promoted internally to a full truth lemma.
-/
theorem hasInternalCountermodel_of_openWeakening_freshCons_truthBySize
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasFreshSigmaConsFromInsertOnFamily (σ := σ)]
    [InternalFO.HasCanonicalTruthBySize (σ := σ)] :
    HasInternalCountermodel σ := by
  letI : InternalFO.HasTruthLemma (σ := σ) := by
    infer_instance
  exact hasInternalCountermodel_of_openWeakening_freshCons_truthLemma (σ := σ)

/--
Build internal countermodels from:
- open weakening,
- sentence-family closure on maximal Lindenbaum members,
- canonical `pi` generalization.

Quantifier truth is recovered internally from:
`HasCanonicalNegImpExtensions + HasCanonicalPiGeneralization`
via the size-recursive canonical truth artifact.
-/
theorem hasInternalCountermodel_of_openWeakening_sentenceFamily_piGeneralization
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasSentenceFamilyClosure (σ := σ)]
    [InternalFO.HasCanonicalPiGeneralization (σ := σ)] :
    HasInternalCountermodel σ := by
  letI : InternalFO.HasFreshSigmaConsFromInsertOnFamily (σ := σ) := by
    infer_instance
  exact hasInternalCountermodel_of_openWeakening_freshCons_piGeneralization (σ := σ)

/--
Build internal countermodels from:
- open weakening,
- closed-theory freshness on maximal Lindenbaum members,
- canonical `pi` generalization.

Quantifier truth is recovered internally from:
`HasCanonicalNegImpExtensions + HasCanonicalPiGeneralization`
via the size-recursive canonical truth artifact.
-/
theorem hasInternalCountermodel_of_openWeakening_theoryClosed_piGeneralization
    [InternalFO.HasOpenWeakening (σ := σ)]
    (hTheoryClosed :
      ∀ {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)},
        M ∈ InternalFO.Lindenbaum.Family (σ := σ) S χ →
        Maximal (· ∈ InternalFO.Lindenbaum.Family (σ := σ) S χ) M →
        ∀ ψ, ψ ∈ M → Syntax.fvFormula (σ := σ) ψ = ∅)
    [InternalFO.HasCanonicalPiGeneralization (σ := σ)] :
    HasInternalCountermodel σ := by
  letI : InternalFO.HasFreshSigmaConsFromInsertOnFamily (σ := σ) :=
    InternalFO.hasFreshSigmaConsFromInsertOnFamily_of_theoryClosed
      (σ := σ)
      (hWeak := InternalFO.HasOpenWeakening.weaken (σ := σ))
      hTheoryClosed
  exact hasInternalCountermodel_of_openWeakening_freshCons_piGeneralization (σ := σ)

/--
Build internal countermodels from:
- open weakening,
- sentence-family closure on maximal Lindenbaum members,
- a full canonical truth lemma.
-/
theorem hasInternalCountermodel_of_openWeakening_sentenceFamily_truthLemma
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasSentenceFamilyClosure (σ := σ)]
    [InternalFO.HasTruthLemma (σ := σ)] :
    HasInternalCountermodel σ := by
  letI : InternalFO.HasFreshSigmaConsFromInsertOnFamily (σ := σ) := by
    infer_instance
  exact hasInternalCountermodel_of_openWeakening_freshCons_truthLemma (σ := σ)

/--
Build internal countermodels from:
- open weakening,
- sentence-family closure on maximal Lindenbaum members,
- canonical truth-by-size.
-/
theorem hasInternalCountermodel_of_openWeakening_sentenceFamily_truthBySize
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasSentenceFamilyClosure (σ := σ)]
    [InternalFO.HasCanonicalTruthBySize (σ := σ)] :
    HasInternalCountermodel σ := by
  letI : InternalFO.HasTruthLemma (σ := σ) := by
    infer_instance
  exact hasInternalCountermodel_of_openWeakening_sentenceFamily_truthLemma (σ := σ)

/--
Fully internal sentence-family route to FO countermodels.

This bundles the canonical chain:
`sentence-family closure -> pi generalization + neg/imp extensions -> truth-by-size -> truth lemma`.
-/
theorem hasInternalCountermodel_of_openWeakening_sentenceFamily
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasSentenceFamilyClosure (σ := σ)] :
    HasInternalCountermodel σ := by
  letI : InternalFO.HasCanonicalTruthBySize (σ := σ) := by
    exact hasCanonicalTruthBySize_of_openWeakening_sentenceFamilyClosure (σ := σ)
  exact hasInternalCountermodel_of_openWeakening_sentenceFamily_truthBySize (σ := σ)

/--
Build internal countermodels from:
- open weakening,
- closed-theory freshness on maximal Lindenbaum members,
- a full canonical truth lemma.
-/
theorem hasInternalCountermodel_of_openWeakening_theoryClosed_truthLemma
    [InternalFO.HasOpenWeakening (σ := σ)]
    (hTheoryClosed :
      ∀ {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)},
        M ∈ InternalFO.Lindenbaum.Family (σ := σ) S χ →
        Maximal (· ∈ InternalFO.Lindenbaum.Family (σ := σ) S χ) M →
        ∀ ψ, ψ ∈ M → Syntax.fvFormula (σ := σ) ψ = ∅)
    [InternalFO.HasTruthLemma (σ := σ)] :
    HasInternalCountermodel σ := by
  letI : InternalFO.HasFreshSigmaConsFromInsertOnFamily (σ := σ) :=
    InternalFO.hasFreshSigmaConsFromInsertOnFamily_of_theoryClosed
      (σ := σ)
      (hWeak := InternalFO.HasOpenWeakening.weaken (σ := σ))
      hTheoryClosed
  exact hasInternalCountermodel_of_openWeakening_freshCons_truthLemma (σ := σ)

/--
Build internal countermodels from:
- open weakening,
- closed-theory freshness on maximal Lindenbaum members,
- canonical truth-by-size.
-/
theorem hasInternalCountermodel_of_openWeakening_theoryClosed_truthBySize
    [InternalFO.HasOpenWeakening (σ := σ)]
    (hTheoryClosed :
      ∀ {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)},
        M ∈ InternalFO.Lindenbaum.Family (σ := σ) S χ →
        Maximal (· ∈ InternalFO.Lindenbaum.Family (σ := σ) S χ) M →
        ∀ ψ, ψ ∈ M → Syntax.fvFormula (σ := σ) ψ = ∅)
    [InternalFO.HasCanonicalTruthBySize (σ := σ)] :
    HasInternalCountermodel σ := by
  letI : InternalFO.HasTruthLemma (σ := σ) := by
    infer_instance
  exact hasInternalCountermodel_of_openWeakening_theoryClosed_truthLemma
    (σ := σ) hTheoryClosed

/--
Build internal countermodels from:
- open weakening,
- global variable-freshness on maximal Lindenbaum members,
- canonical neg/imp extensions,
- canonical quantifier truth.
-/
theorem hasInternalCountermodel_of_openWeakening_globalVarFresh_obligations
    [InternalFO.HasOpenWeakening (σ := σ)]
    (hGlobalVarFresh :
      ∀ {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)},
        M ∈ InternalFO.Lindenbaum.Family (σ := σ) S χ →
        Maximal (· ∈ InternalFO.Lindenbaum.Family (σ := σ) S χ) M →
        ∃ a : Var,
          a ∉ Syntax.fvFormula (σ := σ) χ ∧
          (∀ ψ, ψ ∈ M → a ∉ Syntax.varsFormula (σ := σ) ψ))
    [InternalFO.HasCanonicalNegImpExtensions (σ := σ)]
    [InternalFO.HasCanonicalQuantifierTruth (σ := σ)] :
    HasInternalCountermodel σ := by
  letI : InternalFO.HasExtensionConstruction (σ := σ) :=
    hasExtensionConstruction_of_openWeakening_globalVarFresh
      (σ := σ) hGlobalVarFresh
  letI : InternalFO.HasTruthLemma (σ := σ) := by
    infer_instance
  infer_instance

/--
Build internal countermodels from:
- open weakening,
- finite-support maximal Lindenbaum members,
- canonical neg/imp extensions,
- canonical quantifier truth.
-/
theorem hasInternalCountermodel_of_openWeakening_finiteSupport_obligations
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasFiniteSupportFamily (σ := σ)]
    [InternalFO.HasCanonicalNegImpExtensions (σ := σ)]
    [InternalFO.HasCanonicalQuantifierTruth (σ := σ)] :
    HasInternalCountermodel σ := by
  letI : InternalFO.HasExtensionConstruction (σ := σ) :=
    hasExtensionConstruction_of_openWeakening_finiteSupport (σ := σ)
  letI : InternalFO.HasTruthLemma (σ := σ) := by
    infer_instance
  infer_instance

/--
Direct completeness route from canonical obligations:
- extension construction, and
- canonical neg/imp + quantifier truth obligations.
-/
theorem completeness_from_canonical_obligations
    [InternalFO.HasExtensionConstruction (σ := σ)]
    [InternalFO.HasCanonicalNegImpExtensions (σ := σ)]
    [InternalFO.HasCanonicalQuantifierTruth (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails (σ := σ) Γ φ → Derives (σ := σ) Γ φ :=
  completeness_from_internal_countermodel (σ := σ)

/--
Direct completeness route from the focused internal KripkeFO obligations:
- open weakening for `Derives`,
- fresh-cons witness extraction on Lindenbaum families,
- canonical neg/imp extension obligations,
- canonical quantifier truth obligations.
-/
theorem completeness_from_openWeakening_freshCons_obligations
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasFreshSigmaConsFromInsertOnFamily (σ := σ)]
    [InternalFO.HasCanonicalNegImpExtensions (σ := σ)]
    [InternalFO.HasCanonicalQuantifierTruth (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails (σ := σ) Γ φ → Derives (σ := σ) Γ φ := by
  letI : HasInternalCountermodel σ :=
    hasInternalCountermodel_of_openWeakening_freshCons_obligations (σ := σ)
  exact completeness_from_internal_countermodel (σ := σ)

/--
Direct completeness route from:
- open weakening for `Derives`,
- fresh-cons witness extraction on Lindenbaum families,
- canonical `pi` generalization.

Neg/imp extensions and quantifier truth are reconstructed internally.
-/
theorem completeness_from_openWeakening_freshCons_piGeneralization
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasFreshSigmaConsFromInsertOnFamily (σ := σ)]
    [InternalFO.HasCanonicalPiGeneralization (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails (σ := σ) Γ φ → Derives (σ := σ) Γ φ := by
  letI : HasInternalCountermodel σ :=
    hasInternalCountermodel_of_openWeakening_freshCons_piGeneralization (σ := σ)
  exact completeness_from_internal_countermodel (σ := σ)

/--
Direct completeness route from:
- open weakening for `Derives`,
- fresh-cons witness extraction on Lindenbaum families,
- a full canonical truth lemma.
-/
theorem completeness_from_openWeakening_freshCons_truthLemma
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasFreshSigmaConsFromInsertOnFamily (σ := σ)]
    [InternalFO.HasTruthLemma (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails (σ := σ) Γ φ → Derives (σ := σ) Γ φ := by
  letI : HasInternalCountermodel σ :=
    hasInternalCountermodel_of_openWeakening_freshCons_truthLemma (σ := σ)
  exact completeness_from_internal_countermodel (σ := σ)

/--
Direct completeness route from:
- open weakening for `Derives`,
- fresh-cons witness extraction on Lindenbaum families,
- canonical truth-by-size.
-/
theorem completeness_from_openWeakening_freshCons_truthBySize
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasFreshSigmaConsFromInsertOnFamily (σ := σ)]
    [InternalFO.HasCanonicalTruthBySize (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails (σ := σ) Γ φ → Derives (σ := σ) Γ φ := by
  letI : HasInternalCountermodel σ :=
    hasInternalCountermodel_of_openWeakening_freshCons_truthBySize (σ := σ)
  exact completeness_from_internal_countermodel (σ := σ)

/--
Direct completeness route from the focused internal KripkeFO obligations using tail-fresh extraction.
-/
theorem completeness_from_openWeakening_tailFresh_obligations
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasTailFreshSigmaConsOnFamily (σ := σ)]
    [InternalFO.HasCanonicalNegImpExtensions (σ := σ)]
    [InternalFO.HasCanonicalQuantifierTruth (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails (σ := σ) Γ φ → Derives (σ := σ) Γ φ := by
  letI : HasInternalCountermodel σ :=
    hasInternalCountermodel_of_openWeakening_tailFresh_obligations (σ := σ)
  exact completeness_from_internal_countermodel (σ := σ)

/--
Direct completeness route from:
- open weakening,
- focused tail-fresh extraction on Lindenbaum families,
- canonical `pi` generalization.
-/
theorem completeness_from_openWeakening_tailFresh_piGeneralization
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasTailFreshSigmaConsOnFamily (σ := σ)]
    [InternalFO.HasCanonicalPiGeneralization (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails (σ := σ) Γ φ → Derives (σ := σ) Γ φ := by
  letI : HasInternalCountermodel σ :=
    hasInternalCountermodel_of_openWeakening_tailFresh_piGeneralization (σ := σ)
  exact completeness_from_internal_countermodel (σ := σ)

/--
Direct completeness route from:
- open weakening,
- focused tail-fresh extraction on Lindenbaum families,
- a full canonical truth lemma.
-/
theorem completeness_from_openWeakening_tailFresh_truthLemma
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasTailFreshSigmaConsOnFamily (σ := σ)]
    [InternalFO.HasTruthLemma (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails (σ := σ) Γ φ → Derives (σ := σ) Γ φ := by
  letI : HasInternalCountermodel σ :=
    hasInternalCountermodel_of_openWeakening_tailFresh_truthLemma (σ := σ)
  exact completeness_from_internal_countermodel (σ := σ)

/--
Direct completeness route from:
- open weakening,
- focused tail-fresh extraction on Lindenbaum families,
- canonical truth-by-size.
-/
theorem completeness_from_openWeakening_tailFresh_truthBySize
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasTailFreshSigmaConsOnFamily (σ := σ)]
    [InternalFO.HasCanonicalTruthBySize (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails (σ := σ) Γ φ → Derives (σ := σ) Γ φ := by
  letI : HasInternalCountermodel σ :=
    hasInternalCountermodel_of_openWeakening_tailFresh_truthBySize (σ := σ)
  exact completeness_from_internal_countermodel (σ := σ)

/--
Direct completeness route from:
- open weakening,
- global variable-freshness on maximal Lindenbaum members,
- canonical neg/imp extension obligations,
- canonical quantifier truth obligations.
-/
theorem completeness_from_openWeakening_globalVarFresh_obligations
    [InternalFO.HasOpenWeakening (σ := σ)]
    (hGlobalVarFresh :
      ∀ {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)},
        M ∈ InternalFO.Lindenbaum.Family (σ := σ) S χ →
        Maximal (· ∈ InternalFO.Lindenbaum.Family (σ := σ) S χ) M →
        ∃ a : Var,
          a ∉ Syntax.fvFormula (σ := σ) χ ∧
          (∀ ψ, ψ ∈ M → a ∉ Syntax.varsFormula (σ := σ) ψ))
    [InternalFO.HasCanonicalNegImpExtensions (σ := σ)]
    [InternalFO.HasCanonicalQuantifierTruth (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails (σ := σ) Γ φ → Derives (σ := σ) Γ φ := by
  letI : HasInternalCountermodel σ :=
    hasInternalCountermodel_of_openWeakening_globalVarFresh_obligations
      (σ := σ) hGlobalVarFresh
  exact completeness_from_internal_countermodel (σ := σ)

/--
Direct completeness route from:
- open weakening,
- finite-support maximal Lindenbaum members,
- canonical neg/imp extension obligations,
- canonical quantifier truth obligations.
-/
theorem completeness_from_openWeakening_finiteSupport_obligations
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasFiniteSupportFamily (σ := σ)]
    [InternalFO.HasCanonicalNegImpExtensions (σ := σ)]
    [InternalFO.HasCanonicalQuantifierTruth (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails (σ := σ) Γ φ → Derives (σ := σ) Γ φ := by
  letI : HasInternalCountermodel σ :=
    hasInternalCountermodel_of_openWeakening_finiteSupport_obligations (σ := σ)
  exact completeness_from_internal_countermodel (σ := σ)

/--
Direct completeness route from:
- open weakening,
- sentence-family closure on maximal Lindenbaum members,
- canonical neg/imp extension obligations,
- canonical quantifier truth obligations.
-/
theorem completeness_from_openWeakening_sentenceFamily_obligations
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasSentenceFamilyClosure (σ := σ)]
    [InternalFO.HasCanonicalNegImpExtensions (σ := σ)]
    [InternalFO.HasCanonicalQuantifierTruth (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails (σ := σ) Γ φ → Derives (σ := σ) Γ φ := by
  letI : HasInternalCountermodel σ :=
    hasInternalCountermodel_of_openWeakening_sentenceFamily_obligations (σ := σ)
  exact completeness_from_internal_countermodel (σ := σ)

/--
Direct completeness route from:
- open weakening,
- sentence-family closure on maximal Lindenbaum members,
- canonical `pi` generalization.
-/
theorem completeness_from_openWeakening_sentenceFamily_piGeneralization
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasSentenceFamilyClosure (σ := σ)]
    [InternalFO.HasCanonicalPiGeneralization (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails (σ := σ) Γ φ → Derives (σ := σ) Γ φ := by
  letI : HasInternalCountermodel σ :=
    hasInternalCountermodel_of_openWeakening_sentenceFamily_piGeneralization (σ := σ)
  exact completeness_from_internal_countermodel (σ := σ)

/--
Direct completeness route from:
- open weakening,
- sentence-family closure on maximal Lindenbaum members,
- a full canonical truth lemma.
-/
theorem completeness_from_openWeakening_sentenceFamily_truthLemma
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasSentenceFamilyClosure (σ := σ)]
    [InternalFO.HasTruthLemma (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails (σ := σ) Γ φ → Derives (σ := σ) Γ φ := by
  letI : HasInternalCountermodel σ :=
    hasInternalCountermodel_of_openWeakening_sentenceFamily_truthLemma (σ := σ)
  exact completeness_from_internal_countermodel (σ := σ)

/--
Direct completeness route from:
- open weakening,
- sentence-family closure on maximal Lindenbaum members,
- canonical truth-by-size.
-/
theorem completeness_from_openWeakening_sentenceFamily_truthBySize
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasSentenceFamilyClosure (σ := σ)]
    [InternalFO.HasCanonicalTruthBySize (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails (σ := σ) Γ φ → Derives (σ := σ) Γ φ := by
  letI : HasInternalCountermodel σ :=
    hasInternalCountermodel_of_openWeakening_sentenceFamily_truthBySize (σ := σ)
  exact completeness_from_internal_countermodel (σ := σ)

/--
Direct completeness route from:
- open weakening,
- closed-theory freshness on maximal Lindenbaum members,
- canonical `pi` generalization.
-/
theorem completeness_from_openWeakening_theoryClosed_piGeneralization
    [InternalFO.HasOpenWeakening (σ := σ)]
    (hTheoryClosed :
      ∀ {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)},
        M ∈ InternalFO.Lindenbaum.Family (σ := σ) S χ →
        Maximal (· ∈ InternalFO.Lindenbaum.Family (σ := σ) S χ) M →
        ∀ ψ, ψ ∈ M → Syntax.fvFormula (σ := σ) ψ = ∅)
    [InternalFO.HasCanonicalPiGeneralization (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails (σ := σ) Γ φ → Derives (σ := σ) Γ φ := by
  letI : HasInternalCountermodel σ :=
    hasInternalCountermodel_of_openWeakening_theoryClosed_piGeneralization
      (σ := σ) hTheoryClosed
  exact completeness_from_internal_countermodel (σ := σ)

/--
Direct completeness route from:
- open weakening,
- closed-theory freshness on maximal Lindenbaum members,
- a full canonical truth lemma.
-/
theorem completeness_from_openWeakening_theoryClosed_truthLemma
    [InternalFO.HasOpenWeakening (σ := σ)]
    (hTheoryClosed :
      ∀ {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)},
        M ∈ InternalFO.Lindenbaum.Family (σ := σ) S χ →
        Maximal (· ∈ InternalFO.Lindenbaum.Family (σ := σ) S χ) M →
        ∀ ψ, ψ ∈ M → Syntax.fvFormula (σ := σ) ψ = ∅)
    [InternalFO.HasTruthLemma (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails (σ := σ) Γ φ → Derives (σ := σ) Γ φ := by
  letI : HasInternalCountermodel σ :=
    hasInternalCountermodel_of_openWeakening_theoryClosed_truthLemma
      (σ := σ) hTheoryClosed
  exact completeness_from_internal_countermodel (σ := σ)

/--
Direct completeness route from:
- open weakening,
- closed-theory freshness on maximal Lindenbaum members,
- canonical truth-by-size.
-/
theorem completeness_from_openWeakening_theoryClosed_truthBySize
    [InternalFO.HasOpenWeakening (σ := σ)]
    (hTheoryClosed :
      ∀ {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)},
        M ∈ InternalFO.Lindenbaum.Family (σ := σ) S χ →
        Maximal (· ∈ InternalFO.Lindenbaum.Family (σ := σ) S χ) M →
        ∀ ψ, ψ ∈ M → Syntax.fvFormula (σ := σ) ψ = ∅)
    [InternalFO.HasCanonicalTruthBySize (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails (σ := σ) Γ φ → Derives (σ := σ) Γ φ := by
  letI : HasInternalCountermodel σ :=
    hasInternalCountermodel_of_openWeakening_theoryClosed_truthBySize
      (σ := σ) hTheoryClosed
  exact completeness_from_internal_countermodel (σ := σ)

instance (priority := 100)
    hasInternalCountermodel_of_canonical_obligations
    [InternalFO.HasExtensionConstruction (σ := σ)]
    [InternalFO.HasCanonicalNegImpExtensions (σ := σ)]
    [InternalFO.HasCanonicalQuantifierTruth (σ := σ)] :
    HasInternalCountermodel σ := by
  infer_instance

theorem sound_complete_from_canonical_obligations
    [InternalFO.HasExtensionConstruction (σ := σ)]
    [InternalFO.HasCanonicalNegImpExtensions (σ := σ)]
    [InternalFO.HasCanonicalQuantifierTruth (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Derives (σ := σ) Γ φ ↔ Entails (σ := σ) Γ φ := by
  constructor
  · intro hDer
    exact KripkeFO.soundness (σ := σ) hDer
  · intro hEnt
    exact completeness_from_canonical_obligations (σ := σ) hEnt

/--
Direct sound+completeness route from the focused internal KripkeFO obligations.
-/
theorem sound_complete_from_openWeakening_freshCons_obligations
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasFreshSigmaConsFromInsertOnFamily (σ := σ)]
    [InternalFO.HasCanonicalNegImpExtensions (σ := σ)]
    [InternalFO.HasCanonicalQuantifierTruth (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Derives (σ := σ) Γ φ ↔ Entails (σ := σ) Γ φ := by
  constructor
  · intro hDer
    exact KripkeFO.soundness (σ := σ) hDer
  · intro hEnt
    exact completeness_from_openWeakening_freshCons_obligations (σ := σ) hEnt

/--
Direct sound+completeness route from:
- open weakening,
- fresh-cons witness extraction on Lindenbaum families,
- canonical `pi` generalization.
-/
theorem sound_complete_from_openWeakening_freshCons_piGeneralization
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasFreshSigmaConsFromInsertOnFamily (σ := σ)]
    [InternalFO.HasCanonicalPiGeneralization (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Derives (σ := σ) Γ φ ↔ Entails (σ := σ) Γ φ := by
  constructor
  · intro hDer
    exact KripkeFO.soundness (σ := σ) hDer
  · intro hEnt
    exact completeness_from_openWeakening_freshCons_piGeneralization (σ := σ) hEnt

/--
Direct sound+completeness route from:
- open weakening,
- fresh-cons witness extraction on Lindenbaum families,
- a full canonical truth lemma.
-/
theorem sound_complete_from_openWeakening_freshCons_truthLemma
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasFreshSigmaConsFromInsertOnFamily (σ := σ)]
    [InternalFO.HasTruthLemma (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Derives (σ := σ) Γ φ ↔ Entails (σ := σ) Γ φ := by
  constructor
  · intro hDer
    exact KripkeFO.soundness (σ := σ) hDer
  · intro hEnt
    exact completeness_from_openWeakening_freshCons_truthLemma (σ := σ) hEnt

/--
Direct sound+completeness route from:
- open weakening,
- fresh-cons witness extraction on Lindenbaum families,
- canonical truth-by-size.
-/
theorem sound_complete_from_openWeakening_freshCons_truthBySize
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasFreshSigmaConsFromInsertOnFamily (σ := σ)]
    [InternalFO.HasCanonicalTruthBySize (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Derives (σ := σ) Γ φ ↔ Entails (σ := σ) Γ φ := by
  constructor
  · intro hDer
    exact KripkeFO.soundness (σ := σ) hDer
  · intro hEnt
    exact completeness_from_openWeakening_freshCons_truthBySize (σ := σ) hEnt

/--
Direct sound+completeness route from the focused internal KripkeFO obligations using
tail-fresh extraction.
-/
theorem sound_complete_from_openWeakening_tailFresh_obligations
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasTailFreshSigmaConsOnFamily (σ := σ)]
    [InternalFO.HasCanonicalNegImpExtensions (σ := σ)]
    [InternalFO.HasCanonicalQuantifierTruth (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Derives (σ := σ) Γ φ ↔ Entails (σ := σ) Γ φ := by
  constructor
  · intro hDer
    exact KripkeFO.soundness (σ := σ) hDer
  · intro hEnt
    exact completeness_from_openWeakening_tailFresh_obligations (σ := σ) hEnt

/--
Direct sound+completeness route from:
- open weakening,
- focused tail-fresh extraction on Lindenbaum families,
- canonical `pi` generalization.
-/
theorem sound_complete_from_openWeakening_tailFresh_piGeneralization
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasTailFreshSigmaConsOnFamily (σ := σ)]
    [InternalFO.HasCanonicalPiGeneralization (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Derives (σ := σ) Γ φ ↔ Entails (σ := σ) Γ φ := by
  constructor
  · intro hDer
    exact KripkeFO.soundness (σ := σ) hDer
  · intro hEnt
    exact completeness_from_openWeakening_tailFresh_piGeneralization (σ := σ) hEnt

/--
Direct sound+completeness route from:
- open weakening,
- focused tail-fresh extraction on Lindenbaum families,
- a full canonical truth lemma.
-/
theorem sound_complete_from_openWeakening_tailFresh_truthLemma
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasTailFreshSigmaConsOnFamily (σ := σ)]
    [InternalFO.HasTruthLemma (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Derives (σ := σ) Γ φ ↔ Entails (σ := σ) Γ φ := by
  constructor
  · intro hDer
    exact KripkeFO.soundness (σ := σ) hDer
  · intro hEnt
    exact completeness_from_openWeakening_tailFresh_truthLemma (σ := σ) hEnt

/--
Direct sound+completeness route from:
- open weakening,
- focused tail-fresh extraction on Lindenbaum families,
- canonical truth-by-size.
-/
theorem sound_complete_from_openWeakening_tailFresh_truthBySize
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasTailFreshSigmaConsOnFamily (σ := σ)]
    [InternalFO.HasCanonicalTruthBySize (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Derives (σ := σ) Γ φ ↔ Entails (σ := σ) Γ φ := by
  constructor
  · intro hDer
    exact KripkeFO.soundness (σ := σ) hDer
  · intro hEnt
    exact completeness_from_openWeakening_tailFresh_truthBySize (σ := σ) hEnt

/--
Direct sound+completeness route from:
- open weakening,
- global variable-freshness on maximal Lindenbaum members,
- canonical neg/imp extension obligations,
- canonical quantifier truth obligations.
-/
theorem sound_complete_from_openWeakening_globalVarFresh_obligations
    [InternalFO.HasOpenWeakening (σ := σ)]
    (hGlobalVarFresh :
      ∀ {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)},
        M ∈ InternalFO.Lindenbaum.Family (σ := σ) S χ →
        Maximal (· ∈ InternalFO.Lindenbaum.Family (σ := σ) S χ) M →
        ∃ a : Var,
          a ∉ Syntax.fvFormula (σ := σ) χ ∧
          (∀ ψ, ψ ∈ M → a ∉ Syntax.varsFormula (σ := σ) ψ))
    [InternalFO.HasCanonicalNegImpExtensions (σ := σ)]
    [InternalFO.HasCanonicalQuantifierTruth (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Derives (σ := σ) Γ φ ↔ Entails (σ := σ) Γ φ := by
  constructor
  · intro hDer
    exact KripkeFO.soundness (σ := σ) hDer
  · intro hEnt
    exact completeness_from_openWeakening_globalVarFresh_obligations
      (σ := σ) hGlobalVarFresh hEnt

/--
Direct sound+completeness route from:
- open weakening,
- finite-support maximal Lindenbaum members,
- canonical neg/imp extension obligations,
- canonical quantifier truth obligations.
-/
theorem sound_complete_from_openWeakening_finiteSupport_obligations
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasFiniteSupportFamily (σ := σ)]
    [InternalFO.HasCanonicalNegImpExtensions (σ := σ)]
    [InternalFO.HasCanonicalQuantifierTruth (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Derives (σ := σ) Γ φ ↔ Entails (σ := σ) Γ φ := by
  constructor
  · intro hDer
    exact KripkeFO.soundness (σ := σ) hDer
  · intro hEnt
    exact completeness_from_openWeakening_finiteSupport_obligations (σ := σ) hEnt

/--
Direct sound+completeness route from:
- open weakening,
- sentence-family closure on maximal Lindenbaum members,
- canonical neg/imp extension obligations,
- canonical quantifier truth obligations.
-/
theorem sound_complete_from_openWeakening_sentenceFamily_obligations
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasSentenceFamilyClosure (σ := σ)]
    [InternalFO.HasCanonicalNegImpExtensions (σ := σ)]
    [InternalFO.HasCanonicalQuantifierTruth (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Derives (σ := σ) Γ φ ↔ Entails (σ := σ) Γ φ := by
  constructor
  · intro hDer
    exact KripkeFO.soundness (σ := σ) hDer
  · intro hEnt
    exact completeness_from_openWeakening_sentenceFamily_obligations (σ := σ) hEnt

/--
Direct sound+completeness route from:
- open weakening,
- sentence-family closure on maximal Lindenbaum members,
- canonical `pi` generalization.
-/
theorem sound_complete_from_openWeakening_sentenceFamily_piGeneralization
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasSentenceFamilyClosure (σ := σ)]
    [InternalFO.HasCanonicalPiGeneralization (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Derives (σ := σ) Γ φ ↔ Entails (σ := σ) Γ φ := by
  constructor
  · intro hDer
    exact KripkeFO.soundness (σ := σ) hDer
  · intro hEnt
    exact completeness_from_openWeakening_sentenceFamily_piGeneralization (σ := σ) hEnt

/--
Direct sound+completeness route from:
- open weakening,
- sentence-family closure on maximal Lindenbaum members,
- a full canonical truth lemma.
-/
theorem sound_complete_from_openWeakening_sentenceFamily_truthLemma
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasSentenceFamilyClosure (σ := σ)]
    [InternalFO.HasTruthLemma (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Derives (σ := σ) Γ φ ↔ Entails (σ := σ) Γ φ := by
  constructor
  · intro hDer
    exact KripkeFO.soundness (σ := σ) hDer
  · intro hEnt
    exact completeness_from_openWeakening_sentenceFamily_truthLemma (σ := σ) hEnt

/--
Direct sound+completeness route from:
- open weakening,
- sentence-family closure on maximal Lindenbaum members,
- canonical truth-by-size.
-/
theorem sound_complete_from_openWeakening_sentenceFamily_truthBySize
    [InternalFO.HasOpenWeakening (σ := σ)]
    [InternalFO.HasSentenceFamilyClosure (σ := σ)]
    [InternalFO.HasCanonicalTruthBySize (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Derives (σ := σ) Γ φ ↔ Entails (σ := σ) Γ φ := by
  constructor
  · intro hDer
    exact KripkeFO.soundness (σ := σ) hDer
  · intro hEnt
    exact completeness_from_openWeakening_sentenceFamily_truthBySize (σ := σ) hEnt

/--
Direct sound+completeness route from:
- open weakening,
- closed-theory freshness on maximal Lindenbaum members,
- canonical `pi` generalization.
-/
theorem sound_complete_from_openWeakening_theoryClosed_piGeneralization
    [InternalFO.HasOpenWeakening (σ := σ)]
    (hTheoryClosed :
      ∀ {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)},
        M ∈ InternalFO.Lindenbaum.Family (σ := σ) S χ →
        Maximal (· ∈ InternalFO.Lindenbaum.Family (σ := σ) S χ) M →
        ∀ ψ, ψ ∈ M → Syntax.fvFormula (σ := σ) ψ = ∅)
    [InternalFO.HasCanonicalPiGeneralization (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Derives (σ := σ) Γ φ ↔ Entails (σ := σ) Γ φ := by
  constructor
  · intro hDer
    exact KripkeFO.soundness (σ := σ) hDer
  · intro hEnt
    exact completeness_from_openWeakening_theoryClosed_piGeneralization
      (σ := σ) hTheoryClosed hEnt

/--
Direct sound+completeness route from:
- open weakening,
- closed-theory freshness on maximal Lindenbaum members,
- a full canonical truth lemma.
-/
theorem sound_complete_from_openWeakening_theoryClosed_truthLemma
    [InternalFO.HasOpenWeakening (σ := σ)]
    (hTheoryClosed :
      ∀ {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)},
        M ∈ InternalFO.Lindenbaum.Family (σ := σ) S χ →
        Maximal (· ∈ InternalFO.Lindenbaum.Family (σ := σ) S χ) M →
        ∀ ψ, ψ ∈ M → Syntax.fvFormula (σ := σ) ψ = ∅)
    [InternalFO.HasTruthLemma (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Derives (σ := σ) Γ φ ↔ Entails (σ := σ) Γ φ := by
  constructor
  · intro hDer
    exact KripkeFO.soundness (σ := σ) hDer
  · intro hEnt
    exact completeness_from_openWeakening_theoryClosed_truthLemma
      (σ := σ) hTheoryClosed hEnt

/--
Direct sound+completeness route from:
- open weakening,
- closed-theory freshness on maximal Lindenbaum members,
- canonical truth-by-size.
-/
theorem sound_complete_from_openWeakening_theoryClosed_truthBySize
    [InternalFO.HasOpenWeakening (σ := σ)]
    (hTheoryClosed :
      ∀ {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)},
        M ∈ InternalFO.Lindenbaum.Family (σ := σ) S χ →
        Maximal (· ∈ InternalFO.Lindenbaum.Family (σ := σ) S χ) M →
        ∀ ψ, ψ ∈ M → Syntax.fvFormula (σ := σ) ψ = ∅)
    [InternalFO.HasCanonicalTruthBySize (σ := σ)]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Derives (σ := σ) Γ φ ↔ Entails (σ := σ) Γ φ := by
  constructor
  · intro hDer
    exact KripkeFO.soundness (σ := σ) hDer
  · intro hEnt
    exact completeness_from_openWeakening_theoryClosed_truthBySize
      (σ := σ) hTheoryClosed hEnt

/-!
No standalone global instance is provided in this module.

Downstream code should prefer internal artifacts:
1. provide `HasInternalCountermodel` (or the stronger internal construction classes), then
2. use `completeness` / `sound_complete` below.
-/

theorem completeness [HasInternalCountermodel σ] {Γ : List (Formula σ)} {φ : Formula σ} :
    Entails (σ := σ) Γ φ → Derives (σ := σ) Γ φ :=
  completeness_from_internal_countermodel (σ := σ)

theorem sound_complete [HasInternalCountermodel σ] {Γ : List (Formula σ)} {φ : Formula σ} :
    Derives (σ := σ) Γ φ ↔ Entails (σ := σ) Γ φ := by
  constructor
  · intro hDer
    exact KripkeFO.soundness (σ := σ) hDer
  · intro hEnt
    exact completeness (σ := σ) hEnt

end Completeness
end KripkeFO
end Noneism
end HeytingLean
