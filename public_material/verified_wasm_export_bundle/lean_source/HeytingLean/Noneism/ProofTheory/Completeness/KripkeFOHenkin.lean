import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Zorn
import HeytingLean.Noneism.ProofTheory.NDH
import HeytingLean.Noneism.ProofTheory.Completeness.HenkinCardinalBounds
import HeytingLean.Noneism.ProofTheory.Soundness.KripkeFOHSubst
import HeytingLean.Noneism.Syntax.Henkin
import HeytingLean.Noneism.Semantics.KripkeFOH

namespace HeytingLean
namespace Noneism
namespace HenkinCompleteness

open Syntax.Henkin
open NDH

variable {σ κ : Type}

/--
Set-level derivability for Henkin formulas: finitary context drawn from `T` proving `φ`.
-/
def DerivableH (T : Set (FormulaH σ κ)) (φ : FormulaH σ κ) : Prop :=
  ∃ Γ : List (FormulaH σ κ), (∀ ψ ∈ Γ, ψ ∈ T) ∧ NDH.Derives (σ := σ) (κ := κ) Γ φ

/-! ### Finite-parameter support helpers (for Henkin witness freshness arguments) -/

lemma paramsFormula_subset_paramsContext_of_mem
    {σ κ : Type} [DecidableEq κ]
    {Γ : List (FormulaH σ κ)} {ψ : FormulaH σ κ} (hψ : ψ ∈ Γ) :
    Syntax.Henkin.paramsFormula (σ := σ) (κ := κ) ψ ⊆
      Syntax.Henkin.paramsContext (σ := σ) (κ := κ) Γ := by
  induction Γ with
  | nil =>
      cases hψ
  | cons φ Γ ih =>
      rcases (List.mem_cons.1 hψ) with rfl | hψ'
      ·
        simp [Syntax.Henkin.paramsContext_cons]
      ·
        have :
            Syntax.Henkin.paramsFormula (σ := σ) (κ := κ) ψ ⊆
              Syntax.Henkin.paramsContext (σ := σ) (κ := κ) Γ :=
          ih hψ'
        -- `paramsContext (φ :: Γ) = paramsFormula φ ∪ paramsContext Γ`.
        simpa [Syntax.Henkin.paramsContext_cons] using this.trans Finset.subset_union_right

lemma DerivableH.exists_finite_params
    {σ κ : Type} [DecidableEq κ]
    {T : Set (FormulaH σ κ)} {φ : FormulaH σ κ}
    (h : DerivableH (σ := σ) (κ := κ) T φ) :
    ∃ P : Finset κ,
      Syntax.Henkin.paramsFormula (σ := σ) (κ := κ) φ ⊆ P ∧
      ∃ Γ : List (FormulaH σ κ),
        (∀ ψ ∈ Γ, ψ ∈ T) ∧
        NDH.Derives (σ := σ) (κ := κ) Γ φ ∧
        (∀ ψ ∈ Γ, Syntax.Henkin.paramsFormula (σ := σ) (κ := κ) ψ ⊆ P) := by
  rcases h with ⟨Γ, hΓT, hDer⟩
  classical
  refine ⟨Syntax.Henkin.paramsContext (σ := σ) (κ := κ) Γ ∪
      Syntax.Henkin.paramsFormula (σ := σ) (κ := κ) φ, ?_, ?_⟩
  · exact Finset.subset_union_right
  ·
    refine ⟨Γ, hΓT, hDer, ?_⟩
    intro ψ hψ
    have hψ' :
        Syntax.Henkin.paramsFormula (σ := σ) (κ := κ) ψ ⊆
          Syntax.Henkin.paramsContext (σ := σ) (κ := κ) Γ :=
      paramsFormula_subset_paramsContext_of_mem (σ := σ) (κ := κ) (Γ := Γ) (ψ := ψ) hψ
    exact hψ'.trans Finset.subset_union_left

lemma DerivableH.exists_finite_params_with_fresh
    {σ κ : Type} [DecidableEq κ]
    [HenkinCardinalBounds.HasFreshFromFinset κ]
    {T : Set (FormulaH σ κ)} {φ : FormulaH σ κ}
    (h : DerivableH (σ := σ) (κ := κ) T φ) :
    ∃ k : κ, ∃ P : Finset κ,
      k ∉ P ∧
      Syntax.Henkin.paramsFormula (σ := σ) (κ := κ) φ ⊆ P ∧
      ∃ Γ : List (FormulaH σ κ),
        (∀ ψ ∈ Γ, ψ ∈ T) ∧
        NDH.Derives (σ := σ) (κ := κ) Γ φ ∧
        (∀ ψ ∈ Γ, Syntax.Henkin.paramsFormula (σ := σ) (κ := κ) ψ ⊆ P) := by
  rcases DerivableH.exists_finite_params (σ := σ) (κ := κ) (T := T) (φ := φ) h with
    ⟨P, hφP, Γ, hΓT, hDer, hΓP⟩
  rcases HenkinCardinalBounds.exists_fresh_not_mem_finset (S := P) with ⟨k, hkP⟩
  exact ⟨k, P, hkP, hφP, Γ, hΓT, hDer, hΓP⟩

lemma DerivableH.exists_support_with_fresh_not_mem_params
    {σ κ : Type} [DecidableEq κ]
    [HenkinCardinalBounds.HasFreshFromFinset κ]
    {T : Set (FormulaH σ κ)} {φ : FormulaH σ κ}
    (h : DerivableH (σ := σ) (κ := κ) T φ) :
    ∃ k : κ, ∃ Γ : List (FormulaH σ κ),
      k ∉ Syntax.Henkin.paramsFormula (σ := σ) (κ := κ) φ ∧
      (∀ ψ ∈ Γ, ψ ∈ T) ∧
      NDH.Derives (σ := σ) (κ := κ) Γ φ ∧
      (∀ ψ ∈ Γ, k ∉ Syntax.Henkin.paramsFormula (σ := σ) (κ := κ) ψ) := by
  rcases DerivableH.exists_finite_params_with_fresh
      (σ := σ) (κ := κ) (T := T) (φ := φ) h with
    ⟨k, P, hkP, hφP, Γ, hΓT, hDer, hΓP⟩
  refine ⟨k, Γ, ?_, hΓT, hDer, ?_⟩
  ·
    intro hkφ
    exact hkP (hφP hkφ)
  ·
    intro ψ hψ hkψ
    exact hkP (hΓP ψ hψ hkψ)

lemma derivableH_of_mem {T : Set (FormulaH σ κ)} {φ : FormulaH σ κ} (hφ : φ ∈ T) :
    DerivableH (σ := σ) (κ := κ) T φ := by
  refine ⟨[φ], ?_, ?_⟩
  · intro ψ hψ
    simpa using (show ψ = φ from by simpa using hψ) ▸ hφ
  · exact NDH.Derives.hyp (by simp)

lemma derivableH_of_derives
    {T : Set (FormulaH σ κ)} {Γ : List (FormulaH σ κ)} {φ : FormulaH σ κ}
    (hΓ : ∀ ψ ∈ Γ, ψ ∈ T)
    (hDer : NDH.Derives (σ := σ) (κ := κ) Γ φ) :
    DerivableH (σ := σ) (κ := κ) T φ := by
  exact ⟨Γ, hΓ, hDer⟩

lemma DerivableH.mono {T U : Set (FormulaH σ κ)} {φ : FormulaH σ κ}
    (hTU : T ⊆ U) :
    DerivableH (σ := σ) (κ := κ) T φ →
      DerivableH (σ := σ) (κ := κ) U φ := by
  rintro ⟨Γ, hΓ, hDer⟩
  exact ⟨Γ, (by intro ψ hψ; exact hTU (hΓ ψ hψ)), hDer⟩

/-- Henkin-layer consistency in terms of finite derivability. -/
def ConsistentH (T : Set (FormulaH σ κ)) : Prop :=
  ¬ DerivableH (σ := σ) (κ := κ) T (.bot : FormulaH σ κ)

namespace LindenbaumH

open scoped Classical

/-- Zorn family for Henkin formulas. -/
def FamilyH (S : Set (FormulaH σ κ)) (χ : FormulaH σ κ) : Set (Set (FormulaH σ κ)) :=
  {T | ConsistentH (σ := σ) (κ := κ) T ∧ S ⊆ T ∧ ¬ DerivableH (σ := σ) (κ := κ) T χ}

lemma family_mem_of_base
    {S : Set (FormulaH σ κ)} {χ : FormulaH σ κ}
    (hS : ConsistentH (σ := σ) (κ := κ) S)
    (hχ : ¬ DerivableH (σ := σ) (κ := κ) S χ) :
    S ∈ FamilyH (σ := σ) (κ := κ) S χ := by
  exact ⟨hS, Set.Subset.rfl, hχ⟩

lemma chain_directedOn
    {α : Type} {c : Set (Set α)}
    (hc : IsChain (· ⊆ ·) c) :
    DirectedOn (· ⊆ ·) c := by
  intro a ha b hb
  rcases hc.total ha hb with hab | hba
  · exact ⟨b, hb, hab, subset_rfl⟩
  · exact ⟨a, ha, subset_rfl, hba⟩

lemma sUnion_mem_family
    {S : Set (FormulaH σ κ)} {χ : FormulaH σ κ}
    {c : Set (Set (FormulaH σ κ))}
    (hcF : c ⊆ FamilyH (σ := σ) (κ := κ) S χ)
    (hc : IsChain (· ⊆ ·) c)
    (hcne : c.Nonempty) :
    Set.sUnion c ∈ FamilyH (σ := σ) (κ := κ) S χ := by
  refine ⟨?_, ?_, ?_⟩
  · intro hBot
    rcases hBot with ⟨Γ, hΓ, hDerBot⟩
    let fs : Finset (FormulaH σ κ) := Γ.toFinset
    have hfsfin : (fs : Set (FormulaH σ κ)).Finite := fs.finite_toSet
    have hfsSub : (fs : Set (FormulaH σ κ)) ⊆ Set.sUnion c := by
      intro φ hφ
      have hMemΓ : φ ∈ Γ := List.mem_toFinset.1 hφ
      exact hΓ φ hMemΓ
    have hdir : DirectedOn (· ⊆ ·) c := chain_directedOn (hc := hc)
    rcases DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion
      (α := FormulaH σ κ) (c := c) hcne hdir (s := (fs : Set (FormulaH σ κ)))
      hfsfin hfsSub with ⟨t, htC, hfst⟩
    have hΓt : ∀ ψ ∈ Γ, ψ ∈ t := by
      intro ψ hψ
      have : ψ ∈ (fs : Set (FormulaH σ κ)) := List.mem_toFinset.2 hψ
      exact hfst this
    have htCons : ConsistentH (σ := σ) (κ := κ) t := (hcF htC).1
    exact htCons ⟨Γ, hΓt, hDerBot⟩
  · intro φ hφ
    rcases hcne with ⟨t, htC⟩
    have hSt : S ⊆ t := (hcF htC).2.1
    exact Set.subset_sUnion_of_mem htC (hSt hφ)
  · intro hχ
    rcases hχ with ⟨Γ, hΓ, hDerχ⟩
    let fs : Finset (FormulaH σ κ) := Γ.toFinset
    have hfsfin : (fs : Set (FormulaH σ κ)).Finite := fs.finite_toSet
    have hfsSub : (fs : Set (FormulaH σ κ)) ⊆ Set.sUnion c := by
      intro φ hφ
      have hMemΓ : φ ∈ Γ := List.mem_toFinset.1 hφ
      exact hΓ φ hMemΓ
    have hdir : DirectedOn (· ⊆ ·) c := chain_directedOn (hc := hc)
    rcases DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion
      (α := FormulaH σ κ) (c := c) hcne hdir (s := (fs : Set (FormulaH σ κ)))
      hfsfin hfsSub with ⟨t, htC, hfst⟩
    have hΓt : ∀ ψ ∈ Γ, ψ ∈ t := by
      intro ψ hψ
      have : ψ ∈ (fs : Set (FormulaH σ κ)) := List.mem_toFinset.2 hψ
      exact hfst this
    have htNo : ¬ DerivableH (σ := σ) (κ := κ) t χ := (hcF htC).2.2
    exact htNo ⟨Γ, hΓt, hDerχ⟩

/-- Maximal Henkin-family extension from Zorn. -/
theorem exists_maximal
    (S : Set (FormulaH σ κ)) (χ : FormulaH σ κ)
    (hS : ConsistentH (σ := σ) (κ := κ) S)
    (hχ : ¬ DerivableH (σ := σ) (κ := κ) S χ) :
    ∃ M : Set (FormulaH σ κ),
      S ⊆ M ∧ Maximal (· ∈ FamilyH (σ := σ) (κ := κ) S χ) M := by
  have hmem : S ∈ FamilyH (σ := σ) (κ := κ) S χ :=
    family_mem_of_base (σ := σ) (κ := κ) hS hχ
  have H :
      ∀ c ⊆ FamilyH (σ := σ) (κ := κ) S χ,
        IsChain (· ⊆ ·) c →
          c.Nonempty →
            ∃ ub ∈ FamilyH (σ := σ) (κ := κ) S χ, ∀ s ∈ c, s ⊆ ub := by
    intro c hcF hc hcne
    refine ⟨Set.sUnion c, ?_, ?_⟩
    · exact sUnion_mem_family (σ := σ) (κ := κ) (S := S) (χ := χ)
        (c := c) hcF hc hcne
    · intro s hs
      exact Set.subset_sUnion_of_mem hs
  rcases zorn_subset_nonempty (FamilyH (σ := σ) (κ := κ) S χ) H S hmem with
    ⟨M, hSM, hMax⟩
  exact ⟨M, hSM, hMax⟩

/--
Semantic-cut style transport for Henkin derivability:
if `θ` is derivable from `T` and `χ` is derivable from `insert θ T`,
then `χ` is derivable from `T`.
-/
lemma derivableH_of_insert_of_derivable
    {T : Set (FormulaH σ κ)} {θ χ : FormulaH σ κ}
    (hWeak :
      ∀ {Γ Δ : List (FormulaH σ κ)} {φ : FormulaH σ κ},
        NDH.Derives (σ := σ) (κ := κ) Γ φ →
        Γ ⊆ Δ →
        NDH.Derives (σ := σ) (κ := κ) Δ φ)
    (hθ : DerivableH (σ := σ) (κ := κ) T θ)
    (hχIns : DerivableH (σ := σ) (κ := κ) (Set.insert θ T) χ) :
    DerivableH (σ := σ) (κ := κ) T χ := by
  rcases hθ with ⟨Γθ, hΓθT, hDerθ⟩
  rcases hχIns with ⟨Δ, hΔIns, hDerΔχ⟩
  classical
  let ΔT : List (FormulaH σ κ) := Δ.filter (fun t => decide (t ≠ θ))
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
  have hDerCons : NDH.Derives (σ := σ) (κ := κ) (θ :: ΔT) χ :=
    hWeak hDerΔχ hSubΔ
  have hDerImp : NDH.Derives (σ := σ) (κ := κ) ΔT (.imp θ χ) :=
    NDH.Derives.impI hDerCons
  have hDerImpLift : NDH.Derives (σ := σ) (κ := κ) (ΔT ++ Γθ) (.imp θ χ) :=
    hWeak hDerImp (by
      intro ψ hψ
      exact List.mem_append_left _ hψ)
  have hDerθLift : NDH.Derives (σ := σ) (κ := κ) (ΔT ++ Γθ) θ :=
    hWeak hDerθ (by
      intro ψ hψ
      exact List.mem_append_right _ hψ)
  exact ⟨ΔT ++ Γθ,
    (by
      intro t ht
      rcases List.mem_append.1 ht with htΔT | htΓθ
      · exact hΔTT t htΔT
      · exact hΓθT t htΓθ),
    NDH.Derives.impE hDerImpLift hDerθLift⟩

/--
If inserting `θ` into a family member is not in the family, then `χ` is derivable
from that insertion.
-/
lemma derivableH_chi_of_not_family
    {S : Set (FormulaH σ κ)} {χ : FormulaH σ κ}
    {M : Set (FormulaH σ κ)} {θ : FormulaH σ κ}
    (hMF : M ∈ FamilyH (σ := σ) (κ := κ) S χ)
    (hNotFamIns : Set.insert θ M ∉ FamilyH (σ := σ) (κ := κ) S χ) :
    DerivableH (σ := σ) (κ := κ) (Set.insert θ M) χ := by
  by_contra hNoχ
  have hConsIns : ConsistentH (σ := σ) (κ := κ) (Set.insert θ M) := by
    intro hBotIns
    rcases hBotIns with ⟨Γ, hΓ, hDerBot⟩
    exact hNoχ ⟨Γ, hΓ, NDH.Derives.botE hDerBot⟩
  have hFamIns : Set.insert θ M ∈ FamilyH (σ := σ) (κ := κ) S χ := by
    refine ⟨hConsIns, ?_, hNoχ⟩
    intro t ht
    exact Or.inr ((hMF.2.1) ht)
  exact hNotFamIns hFamIns

/--
Maximal Henkin-family members are deductively closed under `DerivableH`.
-/
lemma closed_of_maximal
    {S : Set (FormulaH σ κ)} {χ : FormulaH σ κ}
    {M : Set (FormulaH σ κ)}
    (hWeak :
      ∀ {Γ Δ : List (FormulaH σ κ)} {φ : FormulaH σ κ},
        NDH.Derives (σ := σ) (κ := κ) Γ φ →
        Γ ⊆ Δ →
        NDH.Derives (σ := σ) (κ := κ) Δ φ)
    (hMF : M ∈ FamilyH (σ := σ) (κ := κ) S χ)
    (hMax : Maximal (· ∈ FamilyH (σ := σ) (κ := κ) S χ) M) :
    ∀ θ : FormulaH σ κ,
      DerivableH (σ := σ) (κ := κ) M θ →
      θ ∈ M := by
  intro θ hDerθ
  by_contra hθNot
  have hCons : ConsistentH (σ := σ) (κ := κ) M := hMF.1
  have hNoχ : ¬ DerivableH (σ := σ) (κ := κ) M χ := hMF.2.2
  have hConsIns : ConsistentH (σ := σ) (κ := κ) (Set.insert θ M) := by
    intro hBotIns
    have hBot : DerivableH (σ := σ) (κ := κ) M (.bot : FormulaH σ κ) :=
      derivableH_of_insert_of_derivable (σ := σ) (κ := κ) hWeak hDerθ hBotIns
    exact hCons hBot
  have hNoχIns : ¬ DerivableH (σ := σ) (κ := κ) (Set.insert θ M) χ := by
    intro hχIns
    have hχM : DerivableH (σ := σ) (κ := κ) M χ :=
      derivableH_of_insert_of_derivable (σ := σ) (κ := κ) hWeak hDerθ hχIns
    exact hNoχ hχM
  have hFamIns : Set.insert θ M ∈ FamilyH (σ := σ) (κ := κ) S χ := by
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
Normalize derivability from `insert θ T` into one-head-context form `θ :: Γ`.
-/
lemma derivesH_cons_of_derivable_insert
    {T : Set (FormulaH σ κ)} {θ χ : FormulaH σ κ}
    (hWeak :
      ∀ {Γ Δ : List (FormulaH σ κ)} {φ : FormulaH σ κ},
        NDH.Derives (σ := σ) (κ := κ) Γ φ →
        Γ ⊆ Δ →
        NDH.Derives (σ := σ) (κ := κ) Δ φ)
    (hχIns : DerivableH (σ := σ) (κ := κ) (Set.insert θ T) χ) :
    ∃ Γ : List (FormulaH σ κ),
      (∀ ψ ∈ Γ, ψ ∈ T) ∧
      NDH.Derives (σ := σ) (κ := κ) (θ :: Γ) χ := by
  rcases hχIns with ⟨Δ, hΔIns, hDerΔχ⟩
  classical
  let Γ : List (FormulaH σ κ) := Δ.filter (fun t => decide (t ≠ θ))
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
From derivability of `χ` after inserting `θ`, derive implication `θ → χ` from `T`.
-/
lemma derivableH_imp_of_derivable_insert
    {T : Set (FormulaH σ κ)} {θ χ : FormulaH σ κ}
    (hWeak :
      ∀ {Γ Δ : List (FormulaH σ κ)} {φ : FormulaH σ κ},
        NDH.Derives (σ := σ) (κ := κ) Γ φ →
        Γ ⊆ Δ →
        NDH.Derives (σ := σ) (κ := κ) Δ φ)
    (hχIns : DerivableH (σ := σ) (κ := κ) (Set.insert θ T) χ) :
    DerivableH (σ := σ) (κ := κ) T (.imp θ χ) := by
  rcases derivesH_cons_of_derivable_insert
    (σ := σ) (κ := κ) (T := T) (θ := θ) (χ := χ) hWeak hχIns with
    ⟨Γ, hΓT, hDerCons⟩
  exact ⟨Γ, hΓT, NDH.Derives.impI hDerCons⟩

/--
From derivability of `⊥` after inserting `θ`, derive `¬ θ` from `T`.
-/
lemma derivableH_not_of_derivable_insert_bot
    {T : Set (FormulaH σ κ)} {θ : FormulaH σ κ}
    (hWeak :
      ∀ {Γ Δ : List (FormulaH σ κ)} {φ : FormulaH σ κ},
        NDH.Derives (σ := σ) (κ := κ) Γ φ →
        Γ ⊆ Δ →
        NDH.Derives (σ := σ) (κ := κ) Δ φ)
    (hBotIns : DerivableH (σ := σ) (κ := κ) (Set.insert θ T) (.bot : FormulaH σ κ)) :
    DerivableH (σ := σ) (κ := κ) T (.not θ) := by
  rcases derivesH_cons_of_derivable_insert
    (σ := σ) (κ := κ) (T := T) (θ := θ) (χ := (.bot : FormulaH σ κ))
    hWeak hBotIns with
    ⟨Γ, hΓT, hDerConsBot⟩
  exact ⟨Γ, hΓT, NDH.Derives.notI hDerConsBot⟩

/--
Maximal Henkin-family members satisfy disjunction primeness.
-/
lemma prime_of_maximal
    {S : Set (FormulaH σ κ)} {χ : FormulaH σ κ}
    {M : Set (FormulaH σ κ)}
    (hWeak :
      ∀ {Γ Δ : List (FormulaH σ κ)} {φ : FormulaH σ κ},
        NDH.Derives (σ := σ) (κ := κ) Γ φ →
        Γ ⊆ Δ →
        NDH.Derives (σ := σ) (κ := κ) Δ φ)
    (hMF : M ∈ FamilyH (σ := σ) (κ := κ) S χ)
    (hMax : Maximal (· ∈ FamilyH (σ := σ) (κ := κ) S χ) M) :
    ∀ φ ψ : FormulaH σ κ, (.or φ ψ) ∈ M → φ ∈ M ∨ ψ ∈ M := by
  intro φ ψ hOrMem
  by_contra hNotPrime
  have hφNot : φ ∉ M := by
    intro hφMem
    exact hNotPrime (Or.inl hφMem)
  have hψNot : ψ ∉ M := by
    intro hψMem
    exact hNotPrime (Or.inr hψMem)

  have hDerIns (th : FormulaH σ κ) (hth : th ∉ M) :
      DerivableH (σ := σ) (κ := κ) (Set.insert th M) χ := by
    have hNotFamIns : Set.insert th M ∉ FamilyH (σ := σ) (κ := κ) S χ := by
      intro hFamIns
      have hSub : M ⊆ Set.insert th M := by
        intro t ht
        exact Or.inr ht
      have hEq : Set.insert th M = M := (hMax.eq_of_subset hFamIns hSub).symm
      exact hth (by
        have : th ∈ Set.insert th M := Or.inl rfl
        simpa [hEq] using this)
    exact derivableH_chi_of_not_family (σ := σ) (κ := κ) (S := S) (χ := χ) (M := M)
      hMF hNotFamIns

  have hImpFrom (th : FormulaH σ κ) (hth : th ∉ M) :
      DerivableH (σ := σ) (κ := κ) M (.imp th χ) :=
    derivableH_imp_of_derivable_insert (σ := σ) (κ := κ) (T := M) (θ := th) (χ := χ)
      hWeak (hDerIns th hth)

  rcases hImpFrom φ hφNot with ⟨Γφ, hΓφM, hDerImpφ⟩
  rcases hImpFrom ψ hψNot with ⟨Γψ, hΓψM, hDerImpψ⟩
  let Δ : List (FormulaH σ κ) := .or φ ψ :: (Γφ ++ Γψ)
  have hDerOr : NDH.Derives (σ := σ) (κ := κ) Δ (.or φ ψ) := NDH.Derives.hyp (by simp [Δ])
  have hDerImpφΔ : NDH.Derives (σ := σ) (κ := κ) Δ (.imp φ χ) :=
    hWeak hDerImpφ (by
      intro θ hθ
      have hθ' : θ ∈ Γφ ++ Γψ := List.mem_append_left _ hθ
      simpa [Δ] using List.mem_cons_of_mem (.or φ ψ) hθ')
  have hDerImpψΔ : NDH.Derives (σ := σ) (κ := κ) Δ (.imp ψ χ) :=
    hWeak hDerImpψ (by
      intro θ hθ
      have hθ' : θ ∈ Γφ ++ Γψ := List.mem_append_right _ hθ
      simpa [Δ] using List.mem_cons_of_mem (.or φ ψ) hθ')
  have hDerLeft : NDH.Derives (σ := σ) (κ := κ) (φ :: Δ) χ := by
    have hDerImpφLeft : NDH.Derives (σ := σ) (κ := κ) (φ :: Δ) (.imp φ χ) :=
      hWeak hDerImpφΔ (by
        intro θ hθ
        exact List.mem_cons_of_mem _ hθ)
    have hDerφLeft : NDH.Derives (σ := σ) (κ := κ) (φ :: Δ) φ :=
      NDH.Derives.hyp (by simp)
    exact NDH.Derives.impE hDerImpφLeft hDerφLeft
  have hDerRight : NDH.Derives (σ := σ) (κ := κ) (ψ :: Δ) χ := by
    have hDerImpψRight : NDH.Derives (σ := σ) (κ := κ) (ψ :: Δ) (.imp ψ χ) :=
      hWeak hDerImpψΔ (by
        intro θ hθ
        exact List.mem_cons_of_mem _ hθ)
    have hDerψRight : NDH.Derives (σ := σ) (κ := κ) (ψ :: Δ) ψ :=
      NDH.Derives.hyp (by simp)
    exact NDH.Derives.impE hDerImpψRight hDerψRight
  have hDerCtxχ : NDH.Derives (σ := σ) (κ := κ) Δ χ :=
    NDH.Derives.orE hDerOr hDerLeft hDerRight
  have hDerivMχ : DerivableH (σ := σ) (κ := κ) M χ := by
    refine ⟨Δ, ?_, hDerCtxχ⟩
    intro t ht
    simp [Δ, List.mem_append] at ht
    rcases ht with rfl | ht | ht
    · exact hOrMem
    · exact hΓφM t ht
    · exact hΓψM t ht
  exact hMF.2.2 hDerivMχ

/--
Henkin-set counterexample extension for negation.

If `¬ φ ∉ M` at a maximal family member `M`, then `insert φ M` is consistent and
can be extended to a maximal member of `FamilyH (insert φ M) ⊥`.
-/
lemma exists_maximal_not_counterexample
    {S : Set (FormulaH σ κ)} {χ : FormulaH σ κ}
    {M : Set (FormulaH σ κ)} {φ : FormulaH σ κ}
    (hWeak :
      ∀ {Γ Δ : List (FormulaH σ κ)} {ψ : FormulaH σ κ},
        NDH.Derives (σ := σ) (κ := κ) Γ ψ →
        Γ ⊆ Δ →
        NDH.Derives (σ := σ) (κ := κ) Δ ψ)
    (hMF : M ∈ FamilyH (σ := σ) (κ := κ) S χ)
    (hMax : Maximal (· ∈ FamilyH (σ := σ) (κ := κ) S χ) M)
    (hNotMem : (.not φ : FormulaH σ κ) ∉ M) :
    ∃ N : Set (FormulaH σ κ),
      Set.insert φ M ⊆ N ∧
      Maximal (· ∈ FamilyH (σ := σ) (κ := κ) (Set.insert φ M) (.bot : FormulaH σ κ)) N := by
  have hClosed :
      ∀ θ : FormulaH σ κ,
        DerivableH (σ := σ) (κ := κ) M θ → θ ∈ M := by
    intro θ hDer
    exact closed_of_maximal
      (σ := σ) (κ := κ) (S := S) (χ := χ) (M := M) hWeak hMF hMax θ hDer
  have hConsIns : ConsistentH (σ := σ) (κ := κ) (Set.insert φ M) := by
    intro hBotIns
    have hNotDer : DerivableH (σ := σ) (κ := κ) M (.not φ) :=
      derivableH_not_of_derivable_insert_bot
        (σ := σ) (κ := κ) (T := M) (θ := φ) hWeak hBotIns
    exact hNotMem (hClosed _ hNotDer)
  have hNoDerBot : ¬ DerivableH (σ := σ) (κ := κ)
      (Set.insert φ M) (.bot : FormulaH σ κ) := hConsIns
  rcases exists_maximal
    (σ := σ) (κ := κ)
    (S := Set.insert φ M)
    (χ := (.bot : FormulaH σ κ))
    hConsIns hNoDerBot with
    ⟨N, hSN, hMaxN⟩
  exact ⟨N, hSN, hMaxN⟩

/--
Henkin-set counterexample extension for implication.

If `(φ → ψ) ∉ M` at a maximal family member `M`, then `insert φ M` can be extended
to a maximal member of `FamilyH (insert φ M) ψ`.
-/
lemma exists_maximal_imp_counterexample
    {S : Set (FormulaH σ κ)} {χ : FormulaH σ κ}
    {M : Set (FormulaH σ κ)} {φ ψ : FormulaH σ κ}
    (hWeak :
      ∀ {Γ Δ : List (FormulaH σ κ)} {ρ : FormulaH σ κ},
        NDH.Derives (σ := σ) (κ := κ) Γ ρ →
        Γ ⊆ Δ →
        NDH.Derives (σ := σ) (κ := κ) Δ ρ)
    (hMF : M ∈ FamilyH (σ := σ) (κ := κ) S χ)
    (hMax : Maximal (· ∈ FamilyH (σ := σ) (κ := κ) S χ) M)
    (hImpNotMem : (.imp φ ψ : FormulaH σ κ) ∉ M) :
    ∃ N : Set (FormulaH σ κ),
      Set.insert φ M ⊆ N ∧
      Maximal (· ∈ FamilyH (σ := σ) (κ := κ) (Set.insert φ M) ψ) N := by
  have hClosed :
      ∀ θ : FormulaH σ κ,
        DerivableH (σ := σ) (κ := κ) M θ → θ ∈ M := by
    intro θ hDer
    exact closed_of_maximal
      (σ := σ) (κ := κ) (S := S) (χ := χ) (M := M) hWeak hMF hMax θ hDer
  have hNoDerPsi :
      ¬ DerivableH (σ := σ) (κ := κ) (Set.insert φ M) ψ := by
    intro hDerPsi
    have hImpDer : DerivableH (σ := σ) (κ := κ) M (.imp φ ψ) :=
      derivableH_imp_of_derivable_insert
        (σ := σ) (κ := κ) (T := M) (θ := φ) (χ := ψ) hWeak hDerPsi
    exact hImpNotMem (hClosed _ hImpDer)
  have hConsIns : ConsistentH (σ := σ) (κ := κ) (Set.insert φ M) := by
    intro hBotIns
    have hDerPsi : DerivableH (σ := σ) (κ := κ) (Set.insert φ M) ψ := by
      rcases hBotIns with ⟨Γ, hΓIns, hDerBot⟩
      exact ⟨Γ, hΓIns, NDH.Derives.botE hDerBot⟩
    exact hNoDerPsi hDerPsi
  rcases exists_maximal
    (σ := σ) (κ := κ)
    (S := Set.insert φ M)
    (χ := ψ)
    hConsIns hNoDerPsi with
    ⟨N, hSN, hMaxN⟩
  exact ⟨N, hSN, hMaxN⟩

end LindenbaumH

/--
Local ND fact: from `(sigma x φ)` and the Henkin witness schema `(sigma x φ -> witnessBody x k φ)`,
derive the witness body.
-/
theorem derives_witnessBody_of_sigma_and_axiom
    {x : Var} {k : κ} {φ : FormulaH σ κ}
    {Γ : List (FormulaH σ κ)} :
    NDH.Derives (σ := σ) (κ := κ) Γ (.sigma x φ) →
    NDH.Derives (σ := σ) (κ := κ) Γ (henkinAxiom x k φ) →
    NDH.Derives (σ := σ) (κ := κ) Γ (witnessBody x k φ) := by
  intro hSigma hAx
  simpa [henkinAxiom, witnessBody] using NDH.Derives.impE hAx hSigma

/-!
## Witness-namespace variants (Track J)

When `κ = Syntax.Henkin.WitParams κw κ0 = Sum κw κ0`, we can reserve `Sum.inl` as a dedicated
namespace for witness constants. This section provides direct analogues of the basic Henkin witness schema
closure lemmas, but using `henkinAxiomSetW` and `witnessBodyW`.
-/

theorem derives_witnessBodyW_of_sigma_and_axiomW
    {κw κ0 : Type}
    {x : Var} {w : κw} {φ : FormulaH σ (Syntax.Henkin.WitParams κw κ0)}
    {Γ : List (FormulaH σ (Syntax.Henkin.WitParams κw κ0))} :
    NDH.Derives (σ := σ) (κ := Syntax.Henkin.WitParams κw κ0) Γ (.sigma x φ) →
    NDH.Derives (σ := σ) (κ := Syntax.Henkin.WitParams κw κ0) Γ
      (Syntax.Henkin.henkinAxiomW (σ := σ) (κw := κw) (κ := κ0) x w φ) →
    NDH.Derives (σ := σ) (κ := Syntax.Henkin.WitParams κw κ0) Γ
      (Syntax.Henkin.witnessBodyW (σ := σ) (κw := κw) (κ := κ0) x w φ) := by
  intro hSigma hAx
  simpa [Syntax.Henkin.henkinAxiomW, Syntax.Henkin.witnessBodyW] using NDH.Derives.impE hAx hSigma

/--
Closed-theory witness extraction:
if `T` is closed under derivability and contains both `(sigma x φ)` and the corresponding
Henkin witness schema, then `T` contains the witness body.
-/
theorem closed_contains_witnessBody_of_sigma
    {T : Set (FormulaH σ κ)} {x : Var} {k : κ} {φ : FormulaH σ κ}
    (hClosed : ∀ θ, DerivableH (σ := σ) (κ := κ) T θ → θ ∈ T)
    (hSigma : (.sigma x φ : FormulaH σ κ) ∈ T)
    (hAxiom : henkinAxiom x k φ ∈ T) :
    witnessBody x k φ ∈ T := by
  let Γ : List (FormulaH σ κ) := [henkinAxiom x k φ, .sigma x φ]
  have hAx : NDH.Derives (σ := σ) (κ := κ) Γ (henkinAxiom x k φ) :=
    NDH.Derives.hyp (by simp [Γ])
  have hSig : NDH.Derives (σ := σ) (κ := κ) Γ (.sigma x φ) :=
    NDH.Derives.hyp (by simp [Γ])
  have hBody : NDH.Derives (σ := σ) (κ := κ) Γ (witnessBody x k φ) :=
    derives_witnessBody_of_sigma_and_axiom (σ := σ) (κ := κ) hSig hAx
  have hΓT : ∀ ψ ∈ Γ, ψ ∈ T := by
    intro ψ hψ
    rcases List.mem_cons.1 hψ with hψAx | hψTail
    · simpa [Γ] using hψAx ▸ hAxiom
    · have hψSigma : ψ = (.sigma x φ : FormulaH σ κ) := by
        simpa [Γ] using hψTail
      simpa [hψSigma] using hSigma
  exact hClosed _ (derivableH_of_derives (σ := σ) (κ := κ) hΓT hBody)

/--
Convenience corollary using a witness-choice function and its generated Henkin witness schema set.
-/
theorem closed_contains_chosen_witnessBody_of_sigma
    {T : Set (FormulaH σ κ)}
    (choose : Var → FormulaH σ κ → κ)
    (hClosed : ∀ θ, DerivableH (σ := σ) (κ := κ) T θ → θ ∈ T)
    (hAxioms : henkinAxiomSet (σ := σ) (κ := κ) choose ⊆ T)
    {x : Var} {φ : FormulaH σ κ}
    (hSigma : (.sigma x φ : FormulaH σ κ) ∈ T) :
    witnessBody x (choose x φ) φ ∈ T := by
  have hAxiom : henkinAxiom x (choose x φ) φ ∈ T := by
    exact hAxioms (by exact ⟨x, φ, rfl⟩)
  exact closed_contains_witnessBody_of_sigma
    (σ := σ) (κ := κ) hClosed hSigma hAxiom

theorem closed_contains_chosen_witnessBodyW_of_sigma
    {κw κ0 : Type}
    {T : Set (FormulaH σ (Syntax.Henkin.WitParams κw κ0))}
    (chooseW : Var → FormulaH σ (Syntax.Henkin.WitParams κw κ0) → κw)
    (hClosed :
      ∀ θ,
        DerivableH (σ := σ) (κ := Syntax.Henkin.WitParams κw κ0) T θ →
          θ ∈ T)
    (hAxioms :
      Syntax.Henkin.henkinAxiomSetW (σ := σ) (κw := κw) (κ := κ0) chooseW ⊆ T)
    {x : Var} {φ : FormulaH σ (Syntax.Henkin.WitParams κw κ0)}
    (hSigma : (.sigma x φ : FormulaH σ (Syntax.Henkin.WitParams κw κ0)) ∈ T) :
    Syntax.Henkin.witnessBodyW (σ := σ) (κw := κw) (κ := κ0) x (chooseW x φ) φ ∈ T := by
  have hAxiom :
      Syntax.Henkin.henkinAxiomW (σ := σ) (κw := κw) (κ := κ0)
          x (chooseW x φ) φ ∈ T := by
    exact hAxioms (by exact ⟨x, φ, rfl⟩)
  exact closed_contains_witnessBody_of_sigma
    (σ := σ) (κ := Syntax.Henkin.WitParams κw κ0)
    (T := T)
    (x := x)
    (k := Sum.inl (chooseW x φ))
    (φ := φ)
    hClosed
    hSigma
    (by
      -- `henkinAxiomW x w φ` is definitionally `henkinAxiom x (Sum.inl w) φ`.
      simpa [Syntax.Henkin.henkinAxiomW, Syntax.Henkin.witnessBodyW, Syntax.Henkin.witTerm,
        Syntax.Henkin.henkinAxiom, Syntax.Henkin.witnessBody] using hAxiom)

/--
Sigma-witness existence from closedness + Henkin witness schemas.

This is the direct replacement for "insert witness into maximal open theory":
the witness is already encoded by `choose`, and closedness gives membership.
-/
theorem exists_witnessBody_of_sigma
    {T : Set (FormulaH σ κ)}
    (choose : Var → FormulaH σ κ → κ)
    (hClosed : ∀ θ, DerivableH (σ := σ) (κ := κ) T θ → θ ∈ T)
    (hAxioms : henkinAxiomSet (σ := σ) (κ := κ) choose ⊆ T)
    {x : Var} {φ : FormulaH σ κ}
    (hSigma : (.sigma x φ : FormulaH σ κ) ∈ T) :
    ∃ k : κ, witnessBody x k φ ∈ T := by
  refine ⟨choose x φ, ?_⟩
  exact closed_contains_chosen_witnessBody_of_sigma
    (σ := σ) (κ := κ) choose hClosed hAxioms hSigma

theorem exists_witnessBodyW_of_sigma
    {κw κ0 : Type}
    {T : Set (FormulaH σ (Syntax.Henkin.WitParams κw κ0))}
    (chooseW : Var → FormulaH σ (Syntax.Henkin.WitParams κw κ0) → κw)
    (hClosed :
      ∀ θ,
        DerivableH (σ := σ) (κ := Syntax.Henkin.WitParams κw κ0) T θ →
          θ ∈ T)
    (hAxioms :
      Syntax.Henkin.henkinAxiomSetW (σ := σ) (κw := κw) (κ := κ0) chooseW ⊆ T)
    {x : Var} {φ : FormulaH σ (Syntax.Henkin.WitParams κw κ0)}
    (hSigma : (.sigma x φ : FormulaH σ (Syntax.Henkin.WitParams κw κ0)) ∈ T) :
    ∃ w : κw,
      Syntax.Henkin.witnessBodyW (σ := σ) (κw := κw) (κ := κ0) x w φ ∈ T := by
  refine ⟨chooseW x φ, ?_⟩
  exact closed_contains_chosen_witnessBodyW_of_sigma
    (σ := σ) (κw := κw) (κ0 := κ0)
    (T := T)
    chooseW
    hClosed
    hAxioms
    hSigma

/--
Closed-theory quantifier elimination helper:
from membership of `pi x φ`, infer membership of any instantiated body `φ[t/x]`.
-/
theorem closed_contains_pi_instance_of_pi
    {T : Set (FormulaH σ κ)} {x : Var} {t : TermH κ} {φ : FormulaH σ κ}
    (hClosed : ∀ θ, DerivableH (σ := σ) (κ := κ) T θ → θ ∈ T)
    (hPi : (.pi x φ : FormulaH σ κ) ∈ T) :
    Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ ∈ T := by
  let Γ : List (FormulaH σ κ) := [.pi x φ]
  have hPiHyp : NDH.Derives (σ := σ) (κ := κ) Γ (.pi x φ) :=
    NDH.Derives.hyp (by simp [Γ])
  have hInst : NDH.Derives (σ := σ) (κ := κ) Γ
      (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ) :=
    NDH.Derives.piE hPiHyp
  have hΓT : ∀ ψ ∈ Γ, ψ ∈ T := by
    intro ψ hψ
    have hψEq : ψ = (.pi x φ : FormulaH σ κ) := by
      simpa [Γ] using hψ
    simpa [hψEq] using hPi
  exact hClosed _ (derivableH_of_derives (σ := σ) (κ := κ) hΓT hInst)

/--
Closed-theory quantifier introduction helper:
from membership of a witness-body instance, infer membership of `sigma x φ`.
-/
theorem closed_contains_sigma_of_witnessBody
    {T : Set (FormulaH σ κ)} {x : Var} {t : TermH κ} {φ : FormulaH σ κ}
    (hClosed : ∀ θ, DerivableH (σ := σ) (κ := κ) T θ → θ ∈ T)
    (hInst : Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ ∈ T) :
    (.sigma x φ : FormulaH σ κ) ∈ T := by
  let Γ : List (FormulaH σ κ) := [Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ]
  have hInstHyp : NDH.Derives (σ := σ) (κ := κ) Γ
      (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ) :=
    NDH.Derives.hyp (by simp [Γ])
  have hSigma : NDH.Derives (σ := σ) (κ := κ) Γ (.sigma x φ) :=
    NDH.Derives.sigmaI hInstHyp
  have hΓT : ∀ ψ ∈ Γ, ψ ∈ T := by
    intro ψ hψ
    have hψEq : ψ = Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ := by
      simpa [Γ] using hψ
    simpa [hψEq] using hInst
  exact hClosed _ (derivableH_of_derives (σ := σ) (κ := κ) hΓT hSigma)

namespace CanonicalH

open LindenbaumH

/--
Henkin canonical world payload extracted from a maximal LindenbaumH family member.

This is the structural object needed for a standalone Henkin canonical-countermodel route.
-/
structure World (σ κ : Type) where
  carrier : Set (FormulaH σ κ)
  consistent : ConsistentH (σ := σ) (κ := κ) carrier
  closed :
    ∀ θ : FormulaH σ κ,
      DerivableH (σ := σ) (κ := κ) carrier θ → θ ∈ carrier
  prime :
    ∀ φ ψ : FormulaH σ κ,
      (.or φ ψ : FormulaH σ κ) ∈ carrier → φ ∈ carrier ∨ ψ ∈ carrier
  sigma_mem_witness :
    ∀ {x : Var} {φ : FormulaH σ κ},
      (.sigma x φ : FormulaH σ κ) ∈ carrier →
        ∃ k : κ, witnessBody x k φ ∈ carrier
  pi_instance_mem :
    ∀ {x : Var} {t : TermH κ} {φ : FormulaH σ κ},
      (.pi x φ : FormulaH σ κ) ∈ carrier →
        Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ ∈ carrier
  /-- Provenance: this world is extracted from a maximal Henkin Lindenbaum family member. -/
  origin :
    ∃ (S : Set (FormulaH σ κ)) (χ : FormulaH σ κ)
      (choose : Var → FormulaH σ κ → κ),
      carrier ∈ FamilyH (σ := σ) (κ := κ) S χ ∧
      Maximal (· ∈ FamilyH (σ := σ) (κ := κ) S χ) carrier ∧
      henkinAxiomSet (σ := σ) (κ := κ) choose ⊆ carrier

instance : LE (World σ κ) := ⟨fun w v => w.carrier ⊆ v.carrier⟩

instance : Preorder (World σ κ) where
  le := (· ≤ ·)
  le_refl _ := Set.Subset.rfl
  le_trans _ _ _ h₁ h₂ := Set.Subset.trans h₁ h₂

/--
Build a Henkin canonical world from a maximal member of `FamilyH`.
-/
def ofMaximal
    (hWeak :
      ∀ {Γ Δ : List (FormulaH σ κ)} {φ : FormulaH σ κ},
        NDH.Derives (σ := σ) (κ := κ) Γ φ →
        Γ ⊆ Δ →
        NDH.Derives (σ := σ) (κ := κ) Δ φ)
    (choose : Var → FormulaH σ κ → κ)
    {S : Set (FormulaH σ κ)} {χ : FormulaH σ κ} {M : Set (FormulaH σ κ)}
    (hMF : M ∈ FamilyH (σ := σ) (κ := κ) S χ)
    (hMax : Maximal (· ∈ FamilyH (σ := σ) (κ := κ) S χ) M)
    (hAxioms : henkinAxiomSet (σ := σ) (κ := κ) choose ⊆ M) :
    World σ κ := by
  refine
    { carrier := M
      consistent := hMF.1
      closed := ?_
      prime := ?_
      sigma_mem_witness := ?_
      pi_instance_mem := ?_
      origin := ⟨S, χ, choose, hMF, hMax, hAxioms⟩ }
  · intro θ hDer
    exact closed_of_maximal (σ := σ) (κ := κ) (S := S) (χ := χ)
      (M := M) hWeak hMF hMax θ hDer
  · intro φ ψ hOr
    exact prime_of_maximal (σ := σ) (κ := κ) (S := S) (χ := χ)
      (M := M) hWeak hMF hMax φ ψ hOr
  · intro x φ hSigma
    exact exists_witnessBody_of_sigma
      (σ := σ) (κ := κ)
      (T := M)
      choose
      (hClosed := by
        intro θ hDer
        exact closed_of_maximal (σ := σ) (κ := κ) (S := S) (χ := χ)
          (M := M) hWeak hMF hMax θ hDer)
      (hAxioms := hAxioms)
      (hSigma := hSigma)
  · intro x t φ hPi
    exact closed_contains_pi_instance_of_pi
      (σ := σ) (κ := κ)
      (T := M)
      (hClosed := by
        intro θ hDer
        exact closed_of_maximal (σ := σ) (κ := κ) (S := S) (χ := χ)
          (M := M) hWeak hMF hMax θ hDer)
      (hPi := hPi)

/--
Negation counterexample extension for canonical worlds built from maximal `FamilyH` members.

If `¬ φ` is not in the current canonical world, we can build an extension world forcing `φ`.
-/
theorem not_counterexample_of_maximal
    (hWeak :
      ∀ {Γ Δ : List (FormulaH σ κ)} {φ : FormulaH σ κ},
        NDH.Derives (σ := σ) (κ := κ) Γ φ →
        Γ ⊆ Δ →
        NDH.Derives (σ := σ) (κ := κ) Δ φ)
    (choose : Var → FormulaH σ κ → κ)
    {S : Set (FormulaH σ κ)} {χ : FormulaH σ κ} {M : Set (FormulaH σ κ)}
    (hMF : M ∈ FamilyH (σ := σ) (κ := κ) S χ)
    (hMax : Maximal (· ∈ FamilyH (σ := σ) (κ := κ) S χ) M)
    (hAxioms : henkinAxiomSet (σ := σ) (κ := κ) choose ⊆ M)
    {φ : FormulaH σ κ}
    (hNotMem : (.not φ : FormulaH σ κ) ∉
        (ofMaximal (σ := σ) (κ := κ) hWeak choose hMF hMax hAxioms).carrier) :
    ∃ v : World σ κ,
      (ofMaximal (σ := σ) (κ := κ) hWeak choose hMF hMax hAxioms) ≤ v ∧
      φ ∈ v.carrier := by
  rcases LindenbaumH.exists_maximal_not_counterexample
    (σ := σ) (κ := κ) (S := S) (χ := χ) (M := M) (φ := φ)
    hWeak hMF hMax (by simpa using hNotMem) with
    ⟨N, hSN, hMaxN⟩
  have hMFN :
      N ∈ FamilyH (σ := σ) (κ := κ) (Set.insert φ M) (.bot : FormulaH σ κ) := hMaxN.prop
  have hAxiomsN : henkinAxiomSet (σ := σ) (κ := κ) choose ⊆ N := by
    intro θ hθ
    exact hSN (Or.inr (hAxioms hθ))
  refine ⟨ofMaximal (σ := σ) (κ := κ) hWeak choose hMFN hMaxN hAxiomsN, ?_, ?_⟩
  · intro θ hθ
    exact hSN (Or.inr hθ)
  · exact hSN (Or.inl rfl)

/--
Implication counterexample extension for canonical worlds built from maximal `FamilyH` members.

If `(φ → ψ)` is not in the current canonical world, we can build an extension world where
`φ` holds but `ψ` is absent.
-/
theorem imp_counterexample_of_maximal
    (hWeak :
      ∀ {Γ Δ : List (FormulaH σ κ)} {ρ : FormulaH σ κ},
        NDH.Derives (σ := σ) (κ := κ) Γ ρ →
        Γ ⊆ Δ →
        NDH.Derives (σ := σ) (κ := κ) Δ ρ)
    (choose : Var → FormulaH σ κ → κ)
    {S : Set (FormulaH σ κ)} {χ : FormulaH σ κ} {M : Set (FormulaH σ κ)}
    (hMF : M ∈ FamilyH (σ := σ) (κ := κ) S χ)
    (hMax : Maximal (· ∈ FamilyH (σ := σ) (κ := κ) S χ) M)
    (hAxioms : henkinAxiomSet (σ := σ) (κ := κ) choose ⊆ M)
    {φ ψ : FormulaH σ κ}
    (hImpNotMem : (.imp φ ψ : FormulaH σ κ) ∉
        (ofMaximal (σ := σ) (κ := κ) hWeak choose hMF hMax hAxioms).carrier) :
    ∃ v : World σ κ,
      (ofMaximal (σ := σ) (κ := κ) hWeak choose hMF hMax hAxioms) ≤ v ∧
      φ ∈ v.carrier ∧
      ψ ∉ v.carrier := by
  rcases LindenbaumH.exists_maximal_imp_counterexample
    (σ := σ) (κ := κ) (S := S) (χ := χ) (M := M) (φ := φ) (ψ := ψ)
    hWeak hMF hMax (by simpa using hImpNotMem) with
    ⟨N, hSN, hMaxN⟩
  have hMFN : N ∈ FamilyH (σ := σ) (κ := κ) (Set.insert φ M) ψ := hMaxN.prop
  have hAxiomsN : henkinAxiomSet (σ := σ) (κ := κ) choose ⊆ N := by
    intro θ hθ
    exact hSN (Or.inr (hAxioms hθ))
  have hPsiNotMem : ψ ∉ N := by
    intro hPsi
    exact hMFN.2.2 (derivableH_of_mem (σ := σ) (κ := κ) hPsi)
  refine
    ⟨ofMaximal (σ := σ) (κ := κ) hWeak choose hMFN hMaxN hAxiomsN, ?_, ?_, ?_⟩
  · intro θ hθ
    exact hSN (Or.inr hθ)
  · exact hSN (Or.inl rfl)
  · simpa using hPsiNotMem

/-- Canonical variable valuation into Henkin terms. -/
def idVarValuation : HeytingLean.Noneism.KripkeFOH.Valuation (TermH κ) :=
  fun x => .var x

/-- Canonical parameter interpretation into Henkin terms. -/
def idParamInterp : HeytingLean.Noneism.KripkeFOH.ParamInterp κ (TermH κ) :=
  fun k => .param k

@[simp] theorem evalTerm_id
    (t : TermH κ) :
    HeytingLean.Noneism.KripkeFOH.evalTerm idVarValuation idParamInterp t = t := by
  cases t <;> rfl

/--
Henkin canonical model over canonical worlds, with domain `TermH κ`.
-/
def model : HeytingLean.Noneism.KripkeFOH.Model (World σ κ) σ (TermH κ) where
  valPred := fun w p args => (.pred p args : FormulaH σ κ) ∈ w.carrier
  monoPred := by
    intro w v hw p args h
    exact hw h
  valEx := fun w t => (.eExists t : FormulaH σ κ) ∈ w.carrier
  monoEx := by
    intro w v hw t h
    exact hw h

@[simp] theorem forces_pred_iff_mem
    (w : World σ κ) (p : σ) (args : List (TermH κ)) :
    HeytingLean.Noneism.KripkeFOH.Forces
      (M := model (σ := σ) (κ := κ))
      idVarValuation
      idParamInterp
      w
      (.pred p args : FormulaH σ κ) ↔
      (.pred p args : FormulaH σ κ) ∈ w.carrier := by
  have hArgs :
      List.map (HeytingLean.Noneism.KripkeFOH.evalTerm idVarValuation idParamInterp) args = args := by
    induction args with
    | nil =>
        simp
    | cons t ts ih =>
        cases t <;> simp [HeytingLean.Noneism.KripkeFOH.evalTerm, idVarValuation, idParamInterp, ih]
  simp [HeytingLean.Noneism.KripkeFOH.Forces, model, hArgs]

@[simp] theorem forces_eExists_iff_mem
    (w : World σ κ) (t : TermH κ) :
    HeytingLean.Noneism.KripkeFOH.Forces
      (M := model (σ := σ) (κ := κ))
      idVarValuation
      idParamInterp
      w
      (.eExists t : FormulaH σ κ) ↔
      (.eExists t : FormulaH σ κ) ∈ w.carrier := by
  simp [HeytingLean.Noneism.KripkeFOH.Forces, model, evalTerm_id]

/--
Canonical-model specialization of the semantic substitution lemma.

This is a key building block for the remaining quantifier-truth obligations in the Henkin
completeness pipeline: it turns `Forces` under an updated valuation into `Forces` of the
syntactic substitution instance.
-/
theorem forces_substFormula_iff
    (w : World σ κ) (x : Var) (t : TermH κ) (φ : FormulaH σ κ) :
    HeytingLean.Noneism.KripkeFOH.Forces
        (M := model (σ := σ) (κ := κ))
        idVarValuation
        idParamInterp
        w (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ) ↔
      HeytingLean.Noneism.KripkeFOH.Forces
        (M := model (σ := σ) (κ := κ))
        (HeytingLean.Noneism.KripkeFOH.update idVarValuation x t)
        idParamInterp
        w φ := by
  -- Use the general lemma proved in `Soundness/KripkeFOHSubst` and simplify `evalTerm` to `t`.
  simpa [HeytingLean.Noneism.KripkeFOH.update_eq_base, evalTerm_id] using
    (HeytingLean.Noneism.KripkeFOH.forces_substFormula
      (M := model (σ := σ) (κ := κ))
      (ρ := idVarValuation)
      (η := idParamInterp)
      (w := w)
      (x := x)
      (t := t)
      (φ := φ))

/--
Canonical `sigma` truth from smaller-formula truth.

This packages both directions (`forcing -> membership` and `membership -> forcing`) into one
reusable step for size-recursive truth-lemma construction.
-/
lemma canonical_sigma_forces_iff_mem_of_lt
    (w : World σ κ) {x : Var} {φ : FormulaH σ κ}
    (hTruthLt :
      ∀ ψ : FormulaH σ κ,
        Syntax.Henkin.fSize (σ := σ) (κ := κ) ψ <
            Syntax.Henkin.fSize (σ := σ) (κ := κ) (.sigma x φ) →
          (HeytingLean.Noneism.KripkeFOH.Forces
              (M := model (σ := σ) (κ := κ))
              idVarValuation idParamInterp w ψ ↔
            ψ ∈ w.carrier)) :
    HeytingLean.Noneism.KripkeFOH.Forces
        (M := model (σ := σ) (κ := κ))
        idVarValuation idParamInterp w (.sigma x φ) ↔
      (.sigma x φ : FormulaH σ κ) ∈ w.carrier := by
  constructor
  · intro hForce
    rcases hForce with ⟨t, hBody⟩
    have hSubstForce :
        HeytingLean.Noneism.KripkeFOH.Forces
          (M := model (σ := σ) (κ := κ))
          idVarValuation idParamInterp w
          (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ) :=
      (forces_substFormula_iff (σ := σ) (κ := κ) w x t φ).2 hBody
    have hSizeEq :
        Syntax.Henkin.fSize (σ := σ) (κ := κ)
            (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ) =
          Syntax.Henkin.fSize (σ := σ) (κ := κ) φ :=
      Syntax.Henkin.fSize_substFormula (σ := σ) (κ := κ) x t φ
    have hSizeLt :
        Syntax.Henkin.fSize (σ := σ) (κ := κ)
            (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ) <
          Syntax.Henkin.fSize (σ := σ) (κ := κ) (.sigma x φ) := by
      simp [Syntax.Henkin.fSize, hSizeEq]
    have hSubstMem :
        Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ ∈ w.carrier :=
      (hTruthLt _ hSizeLt).1 hSubstForce
    have hDerSubst :
        DerivableH (σ := σ) (κ := κ) w.carrier
          (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ) :=
      derivableH_of_mem (σ := σ) (κ := κ) hSubstMem
    have hDerSigma : DerivableH (σ := σ) (κ := κ) w.carrier (.sigma x φ) := by
      rcases hDerSubst with ⟨Γ, hΓMem, hDerΓ⟩
      exact ⟨Γ, hΓMem, NDH.Derives.sigmaI (x := x) (t := t) (φ := φ) hDerΓ⟩
    exact w.closed _ hDerSigma
  · intro hSigma
    rcases w.sigma_mem_witness (x := x) (φ := φ) hSigma with ⟨k, hkMem⟩
    have hSizeEq :
        Syntax.Henkin.fSize (σ := σ) (κ := κ)
            (Syntax.Henkin.witnessBody (σ := σ) (κ := κ) x k φ) =
          Syntax.Henkin.fSize (σ := σ) (κ := κ) φ := by
      simpa [Syntax.Henkin.witnessBody] using
        (Syntax.Henkin.fSize_substFormula (σ := σ) (κ := κ) x (.param k) φ)
    have hSizeLt :
        Syntax.Henkin.fSize (σ := σ) (κ := κ)
            (Syntax.Henkin.witnessBody (σ := σ) (κ := κ) x k φ) <
          Syntax.Henkin.fSize (σ := σ) (κ := κ) (.sigma x φ) := by
      simp [Syntax.Henkin.fSize, hSizeEq]
    have hWitnessForce :
        HeytingLean.Noneism.KripkeFOH.Forces
          (M := model (σ := σ) (κ := κ))
          idVarValuation idParamInterp w
          (Syntax.Henkin.witnessBody (σ := σ) (κ := κ) x k φ) :=
      (hTruthLt _ hSizeLt).2 hkMem
    refine ⟨(.param k : TermH κ), ?_⟩
    -- Rewrite witness-body forcing to forcing of the quantifier body under the updated valuation.
    exact (forces_substFormula_iff (σ := σ) (κ := κ) w x (.param k) φ).1 hWitnessForce

/--
Canonical `pi` truth at `w` from:
- smaller-formula truth on all extensions `v ≥ w`, and
- extension-stable `pi`-generalization (from membership of all instances to membership of `pi`).
-/
lemma canonical_pi_forces_iff_mem_of_lt_and_generalization_on_extensions
    (w : World σ κ) {x : Var} {φ : FormulaH σ κ}
    (hTruthLt :
      ∀ v : World σ κ, w ≤ v →
        ∀ ψ : FormulaH σ κ,
          Syntax.Henkin.fSize (σ := σ) (κ := κ) ψ <
              Syntax.Henkin.fSize (σ := σ) (κ := κ) (.pi x φ) →
            (HeytingLean.Noneism.KripkeFOH.Forces
                (M := model (σ := σ) (κ := κ))
                idVarValuation idParamInterp v ψ ↔
              ψ ∈ v.carrier))
    (hPiGeneralize :
      ∀ v : World σ κ, w ≤ v →
        (∀ t : TermH κ,
          Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ ∈ v.carrier) →
        (.pi x φ : FormulaH σ κ) ∈ v.carrier) :
    HeytingLean.Noneism.KripkeFOH.Forces
        (M := model (σ := σ) (κ := κ))
        idVarValuation idParamInterp w (.pi x φ) ↔
      (.pi x φ : FormulaH σ κ) ∈ w.carrier := by
  constructor
  · intro hForce
    apply hPiGeneralize w (by rfl)
    intro t
    have hBody :
        HeytingLean.Noneism.KripkeFOH.Forces
          (M := model (σ := σ) (κ := κ))
          (HeytingLean.Noneism.KripkeFOH.update idVarValuation x t)
          idParamInterp w φ :=
      hForce w (by rfl) t
    have hSubstForce :
        HeytingLean.Noneism.KripkeFOH.Forces
          (M := model (σ := σ) (κ := κ))
          idVarValuation idParamInterp w
          (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ) :=
      (forces_substFormula_iff (σ := σ) (κ := κ) w x t φ).2 hBody
    have hSizeEq :
        Syntax.Henkin.fSize (σ := σ) (κ := κ)
            (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ) =
          Syntax.Henkin.fSize (σ := σ) (κ := κ) φ :=
      Syntax.Henkin.fSize_substFormula (σ := σ) (κ := κ) x t φ
    have hSizeLt :
        Syntax.Henkin.fSize (σ := σ) (κ := κ)
            (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ) <
          Syntax.Henkin.fSize (σ := σ) (κ := κ) (.pi x φ) := by
      simp [Syntax.Henkin.fSize, hSizeEq]
    exact (hTruthLt w (by rfl) _ hSizeLt).1 hSubstForce
  · intro hPiMem v hwv t
    have hPiMemV : (.pi x φ : FormulaH σ κ) ∈ v.carrier := hwv hPiMem
    have hInstMem :
        Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ ∈ v.carrier :=
      v.pi_instance_mem (x := x) (t := t) (φ := φ) hPiMemV
    have hSizeEq :
        Syntax.Henkin.fSize (σ := σ) (κ := κ)
            (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ) =
          Syntax.Henkin.fSize (σ := σ) (κ := κ) φ :=
      Syntax.Henkin.fSize_substFormula (σ := σ) (κ := κ) x t φ
    have hSizeLt :
        Syntax.Henkin.fSize (σ := σ) (κ := κ)
            (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ) <
          Syntax.Henkin.fSize (σ := σ) (κ := κ) (.pi x φ) := by
      simp [Syntax.Henkin.fSize, hSizeEq]
    have hInstForce :
        HeytingLean.Noneism.KripkeFOH.Forces
          (M := model (σ := σ) (κ := κ))
          idVarValuation idParamInterp v
          (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ) :=
      (hTruthLt v hwv _ hSizeLt).2 hInstMem
    exact (forces_substFormula_iff (σ := σ) (κ := κ) v x t φ).1 hInstForce

end CanonicalH

namespace InternalH

open CanonicalH

/--
Internal structural obligation: unrestricted list-context weakening for `NDH.Derives`.
-/
class HasOpenWeakening (σ : Type) (κ : Type) : Prop where
  weaken :
    ∀ {Γ Δ : List (FormulaH σ κ)} {φ : FormulaH σ κ},
      NDH.Derives (σ := σ) (κ := κ) Γ φ →
      Γ ⊆ Δ →
      NDH.Derives (σ := σ) (κ := κ) Δ φ

instance (priority := 100)
    hasOpenWeakening_of_nd :
    HasOpenWeakening σ κ where
  weaken := by
    intro Γ Δ φ hDer hSub
    exact NDH.Derives.wk hDer hSub

/--
Bridge obligation from list sequents to set-based Henkin Lindenbaum base facts.
-/
class HasSequentFamilyBase (σ : Type) (κ : Type) : Prop where
  base_consistent :
    ∀ {Γ : List (FormulaH σ κ)} {φ : FormulaH σ κ},
      ¬ NDH.Derives (σ := σ) (κ := κ) Γ φ →
        ConsistentH (σ := σ) (κ := κ) (fun ψ => ψ ∈ Γ)
  base_notDerivable :
    ∀ {Γ : List (FormulaH σ κ)} {φ : FormulaH σ κ},
      ¬ NDH.Derives (σ := σ) (κ := κ) Γ φ →
        ¬ DerivableH (σ := σ) (κ := κ) (fun ψ => ψ ∈ Γ) φ

instance (priority := 95)
    hasSequentFamilyBase_of_openWeakening
    [HasOpenWeakening σ κ] :
    HasSequentFamilyBase σ κ where
  base_consistent := by
    intro Γ φ hNotDer hInconsistent
    rcases hInconsistent with ⟨Δ, hΔS, hDerBot⟩
    have hSub : Δ ⊆ Γ := by
      intro ψ hψ
      exact hΔS ψ hψ
    have hDerBotΓ :
        NDH.Derives (σ := σ) (κ := κ) Γ (.bot : FormulaH σ κ) :=
      HasOpenWeakening.weaken (σ := σ) (κ := κ) hDerBot hSub
    exact hNotDer (NDH.Derives.botE hDerBotΓ)
  base_notDerivable := by
    intro Γ φ hNotDer hDerivable
    rcases hDerivable with ⟨Δ, hΔS, hDerΔ⟩
    have hSub : Δ ⊆ Γ := by
      intro ψ hψ
      exact hΔS ψ hψ
    have hDerΓ : NDH.Derives (σ := σ) (κ := κ) Γ φ :=
      HasOpenWeakening.weaken (σ := σ) (κ := κ) hDerΔ hSub
    exact hNotDer hDerΓ

/--
Maximal Henkin-family extension for a non-derivable list sequent.
-/
theorem exists_maximal_of_not_derives
    [HasSequentFamilyBase σ κ]
    {Γ : List (FormulaH σ κ)} {φ : FormulaH σ κ}
    (hNotDer : ¬ NDH.Derives (σ := σ) (κ := κ) Γ φ) :
    ∃ M : Set (FormulaH σ κ),
      (∀ ψ, ψ ∈ Γ → ψ ∈ M) ∧
      Maximal
        (· ∈ LindenbaumH.FamilyH
          (σ := σ) (κ := κ) (fun ψ : FormulaH σ κ => ψ ∈ Γ) φ) M := by
  have hSCons : ConsistentH (σ := σ) (κ := κ) (fun ψ : FormulaH σ κ => ψ ∈ Γ) :=
    HasSequentFamilyBase.base_consistent (σ := σ) (κ := κ) (Γ := Γ) (φ := φ) hNotDer
  have hSNot : ¬ DerivableH (σ := σ) (κ := κ) (fun ψ : FormulaH σ κ => ψ ∈ Γ) φ :=
    HasSequentFamilyBase.base_notDerivable (σ := σ) (κ := κ) (Γ := Γ) (φ := φ) hNotDer
  exact LindenbaumH.exists_maximal
    (σ := σ) (κ := κ) (S := (fun ψ : FormulaH σ κ => ψ ∈ Γ)) (χ := φ) hSCons hSNot

/--
Henkinized base obligation for extension construction:
close list-context sequents under a chosen Henkin witness schema set while preserving
consistency and non-derivability of the goal.
-/
class HasHenkinizedFamilyBase (σ : Type) (κ : Type) where
  henkinize :
    ∀ {Γ : List (FormulaH σ κ)} {φ : FormulaH σ κ},
      ¬ NDH.Derives (σ := σ) (κ := κ) Γ φ →
        ∃ choose : Var → FormulaH σ κ → κ,
          ConsistentH (σ := σ) (κ := κ)
            (fun ψ => ψ ∈ Γ ∨ ψ ∈ henkinAxiomSet (σ := σ) (κ := κ) choose) ∧
          ¬ DerivableH (σ := σ) (κ := κ)
            (fun ψ => ψ ∈ Γ ∨ ψ ∈ henkinAxiomSet (σ := σ) (κ := κ) choose) φ

/--
Build a Henkin-layer canonical countermodel from two internal ingredients:
1) extension of non-derivable sequents to carrier-membership/non-membership;
2) canonical truth lemma (`Forces` iff carrier membership).
-/
theorem countermodel_of_extension_and_truth
    {Γ : List (FormulaH σ κ)} {φ : FormulaH σ κ}
    (hExtend :
      ¬ NDH.Derives (σ := σ) (κ := κ) Γ φ →
        ∃ w : World σ κ,
          (∀ ψ ∈ Γ, ψ ∈ w.carrier) ∧
          φ ∉ w.carrier)
    (hTruth :
      ∀ (w : World σ κ) (ψ : FormulaH σ κ),
        HeytingLean.Noneism.KripkeFOH.Forces
          (M := model (σ := σ) (κ := κ))
          idVarValuation
          idParamInterp
          w ψ ↔
        ψ ∈ w.carrier) :
    ¬ NDH.Derives (σ := σ) (κ := κ) Γ φ →
      ∃ w : World σ κ,
        (∀ ψ ∈ Γ,
          HeytingLean.Noneism.KripkeFOH.Forces
            (M := model (σ := σ) (κ := κ))
            idVarValuation
            idParamInterp
            w ψ) ∧
        ¬ HeytingLean.Noneism.KripkeFOH.Forces
          (M := model (σ := σ) (κ := κ))
          idVarValuation
          idParamInterp
          w φ := by
  intro hNotDer
  rcases hExtend hNotDer with ⟨w, hΓMem, hNotMem⟩
  refine ⟨w, ?_, ?_⟩
  · intro ψ hψ
    exact (hTruth w ψ).2 (hΓMem ψ hψ)
  · intro hForce
    exact hNotMem ((hTruth w φ).1 hForce)

/--
Internal Henkin obligation A: extend non-derivable sequents to canonical carriers.
-/
class HasExtensionConstruction (σ : Type) (κ : Type) : Prop where
  extend_avoid :
    ∀ {Γ : List (FormulaH σ κ)} {φ : FormulaH σ κ},
      ¬ NDH.Derives (σ := σ) (κ := κ) Γ φ →
        ∃ w : World σ κ,
          (∀ ψ ∈ Γ, ψ ∈ w.carrier) ∧
          φ ∉ w.carrier

instance (priority := 85)
    hasExtensionConstruction_of_henkinized_base
    [HasOpenWeakening σ κ]
    [HasHenkinizedFamilyBase σ κ] :
    HasExtensionConstruction σ κ where
  extend_avoid := by
    intro Γ φ hNotDer
    rcases HasHenkinizedFamilyBase.henkinize (σ := σ) (κ := κ) (Γ := Γ) (φ := φ) hNotDer with
      ⟨choose, hSCons, hSNot⟩
    let S : Set (FormulaH σ κ) :=
      fun ψ => ψ ∈ Γ ∨ ψ ∈ henkinAxiomSet (σ := σ) (κ := κ) choose
    rcases LindenbaumH.exists_maximal
      (σ := σ) (κ := κ) (S := S) (χ := φ) hSCons hSNot with
      ⟨M, hSM, hMax⟩
    have hMF : M ∈ LindenbaumH.FamilyH (σ := σ) (κ := κ) S φ := hMax.prop
    have hAxioms : henkinAxiomSet (σ := σ) (κ := κ) choose ⊆ M := by
      intro ψ hψ
      exact hSM (Or.inr hψ)
    have hNotMem : φ ∉ M := by
      intro hφMem
      exact hMF.2.2 (derivableH_of_mem (σ := σ) (κ := κ) hφMem)
    refine
      ⟨CanonicalH.ofMaximal
        (σ := σ) (κ := κ)
        (hWeak := HasOpenWeakening.weaken (σ := σ) (κ := κ))
        choose hMF hMax hAxioms, ?_, ?_⟩
    · intro ψ hψ
      exact hSM (Or.inl hψ)
    · simpa using hNotMem

/--
Internal Henkin obligation B: canonical truth lemma over `FormulaH`.
-/
class HasTruthLemma (σ : Type) (κ : Type) : Prop where
  truth_iff_mem :
    ∀ (w : World σ κ) (ψ : FormulaH σ κ),
      HeytingLean.Noneism.KripkeFOH.Forces
        (M := model (σ := σ) (κ := κ))
        idVarValuation
        idParamInterp
        w ψ ↔
      ψ ∈ w.carrier

/--
Counterexample obligations for canonical `not`/`imp` truth over `FormulaH`.
-/
class HasCanonicalNegImpExtensions (σ : Type) (κ : Type) : Prop where
  not_counterexample :
    ∀ {w : World σ κ} {φ : FormulaH σ κ},
      (.not φ : FormulaH σ κ) ∉ w.carrier →
        ∃ v : World σ κ, w ≤ v ∧ φ ∈ v.carrier
  imp_counterexample :
    ∀ {w : World σ κ} {φ ψ : FormulaH σ κ},
      (.imp φ ψ : FormulaH σ κ) ∉ w.carrier →
        ∃ v : World σ κ, w ≤ v ∧ φ ∈ v.carrier ∧ ψ ∉ v.carrier

/--
Quantifier obligations for canonical `sigma`/`pi` truth over `FormulaH`.
-/
class HasCanonicalQuantifierTruth (σ : Type) (κ : Type) : Prop where
  sigma_forces_iff_mem :
    ∀ (w : World σ κ) (x : Var) (φ : FormulaH σ κ),
      HeytingLean.Noneism.KripkeFOH.Forces
        (M := model (σ := σ) (κ := κ))
        idVarValuation
        idParamInterp
        w (.sigma x φ) ↔
      (.sigma x φ : FormulaH σ κ) ∈ w.carrier
  pi_forces_iff_mem :
    ∀ (w : World σ κ) (x : Var) (φ : FormulaH σ κ),
      HeytingLean.Noneism.KripkeFOH.Forces
        (M := model (σ := σ) (κ := κ))
        idVarValuation
        idParamInterp
        w (.pi x φ) ↔
      (.pi x φ : FormulaH σ κ) ∈ w.carrier

instance (priority := 80)
    hasCanonicalQuantifierTruth_of_truthLemma
    [HasTruthLemma σ κ] :
    HasCanonicalQuantifierTruth σ κ where
  sigma_forces_iff_mem := by
    intro w x φ
    exact HasTruthLemma.truth_iff_mem (σ := σ) (κ := κ) w (.sigma x φ)
  pi_forces_iff_mem := by
    intro w x φ
    exact HasTruthLemma.truth_iff_mem (σ := σ) (κ := κ) w (.pi x φ)

instance (priority := 100)
    hasCanonicalNegImpExtensions_of_origin
    [HasOpenWeakening σ κ] :
    HasCanonicalNegImpExtensions σ κ where
  not_counterexample := by
    intro w φ hNotMem
    rcases w.origin with ⟨S, χ, choose, hMF, hMax, hAxioms⟩
    let w0 : World σ κ :=
      CanonicalH.ofMaximal
        (σ := σ) (κ := κ)
        (hWeak := HasOpenWeakening.weaken (σ := σ) (κ := κ))
        (choose := choose)
        (hMF := hMF)
        (hMax := hMax)
        (hAxioms := hAxioms)
    have hw_w0 : w ≤ w0 := by
      intro θ hθ
      simpa [w0, CanonicalH.ofMaximal]
        using hθ
    have hNotMem0 : (.not φ : FormulaH σ κ) ∉ w0.carrier := by
      simpa [w0, CanonicalH.ofMaximal]
        using hNotMem
    rcases CanonicalH.not_counterexample_of_maximal
      (σ := σ) (κ := κ)
      (hWeak := HasOpenWeakening.weaken (σ := σ) (κ := κ))
      (choose := choose)
      (hMF := hMF)
      (hMax := hMax)
      (hAxioms := hAxioms)
      (φ := φ)
      hNotMem0 with ⟨v, hw0v, hφv⟩
    exact ⟨v, Preorder.le_trans _ _ _ hw_w0 hw0v, hφv⟩
  imp_counterexample := by
    intro w φ ψ hImpNotMem
    rcases w.origin with ⟨S, χ, choose, hMF, hMax, hAxioms⟩
    let w0 : World σ κ :=
      CanonicalH.ofMaximal
        (σ := σ) (κ := κ)
        (hWeak := HasOpenWeakening.weaken (σ := σ) (κ := κ))
        (choose := choose)
        (hMF := hMF)
        (hMax := hMax)
        (hAxioms := hAxioms)
    have hw_w0 : w ≤ w0 := by
      intro θ hθ
      simpa [w0, CanonicalH.ofMaximal]
        using hθ
    have hImpNotMem0 : (.imp φ ψ : FormulaH σ κ) ∉ w0.carrier := by
      simpa [w0, CanonicalH.ofMaximal]
        using hImpNotMem
    rcases CanonicalH.imp_counterexample_of_maximal
      (σ := σ) (κ := κ)
      (hWeak := HasOpenWeakening.weaken (σ := σ) (κ := κ))
      (choose := choose)
      (hMF := hMF)
      (hMax := hMax)
      (hAxioms := hAxioms)
      (φ := φ)
      (ψ := ψ)
      hImpNotMem0 with ⟨v, hw0v, hφv, hψv⟩
    exact ⟨v, Preorder.le_trans _ _ _ hw_w0 hw0v, hφv, hψv⟩

/--
Canonical `pi` generalization obligation for Henkin canonical worlds.

This is the remaining `pi`-side artifact needed by the size-recursive canonical truth lemma:
if a world contains all substitution instances of the body, it contains the `pi` formula itself.
-/
class HasCanonicalPiGeneralization (σ : Type) (κ : Type) : Prop where
  pi_generalize :
    ∀ (w : World σ κ) (x : Var) (φ : FormulaH σ κ),
      (∀ t : TermH κ,
        Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ ∈ w.carrier) →
      (.pi x φ : FormulaH σ κ) ∈ w.carrier

/--
Canonical truth oracle on strictly smaller formulas (by `Syntax.Henkin.fSize`).

This isolates the well-founded recursion artifact used to close quantifier truth internally.
-/
class HasCanonicalTruthBySize (σ : Type) (κ : Type) : Prop where
  truth_lt :
    ∀ (n : Nat) (w : World σ κ) (ψ : FormulaH σ κ),
      Syntax.Henkin.fSize (σ := σ) (κ := κ) ψ < n →
        (HeytingLean.Noneism.KripkeFOH.Forces
            (M := model (σ := σ) (κ := κ))
            idVarValuation idParamInterp w ψ ↔
          ψ ∈ w.carrier)

/--
If the full canonical truth lemma is available, `pi`-generalization follows semantically:
instance-membership at `w` lifts to all extensions by monotonicity, then forcing of `pi` yields
membership via truth.
-/
instance (priority := 100)
    hasCanonicalPiGeneralization_of_truthLemma
    [HasTruthLemma σ κ] :
    HasCanonicalPiGeneralization σ κ where
  pi_generalize := by
    intro w x φ hAllInst
    have hPiForce :
        HeytingLean.Noneism.KripkeFOH.Forces
          (M := model (σ := σ) (κ := κ))
          idVarValuation
          idParamInterp
          w (.pi x φ) := by
      intro v hwv t
      have hInstMemV :
          Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ ∈ v.carrier :=
        hwv (hAllInst t)
      have hSubstForce :
          HeytingLean.Noneism.KripkeFOH.Forces
            (M := model (σ := σ) (κ := κ))
            idVarValuation
            idParamInterp
            v (Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ) :=
        (HasTruthLemma.truth_iff_mem (σ := σ) (κ := κ)
          (w := v)
          (ψ := Syntax.Henkin.substFormula (σ := σ) (κ := κ) x t φ)).2 hInstMemV
      exact (CanonicalH.forces_substFormula_iff (σ := σ) (κ := κ) v x t φ).1 hSubstForce
    exact (HasTruthLemma.truth_iff_mem (σ := σ) (κ := κ) (w := w) (ψ := .pi x φ)).1 hPiForce

instance (priority := 100)
    hasCanonicalTruthBySize_of_truthLemma
    [HasTruthLemma σ κ] :
    HasCanonicalTruthBySize σ κ where
  truth_lt := by
    intro _n w ψ _hlt
    exact HasTruthLemma.truth_iff_mem (σ := σ) (κ := κ) w ψ

instance (priority := 99)
    hasTruthLemma_of_truthBySize
    [HasCanonicalTruthBySize σ κ] :
    HasTruthLemma σ κ where
  truth_iff_mem := by
    intro w ψ
    exact HasCanonicalTruthBySize.truth_lt
      (σ := σ) (κ := κ)
      (n := Syntax.Henkin.fSize (σ := σ) (κ := κ) ψ + 1)
      (w := w)
      (ψ := ψ)
      (Nat.lt_succ_self _)

set_option linter.unnecessarySimpa false
/--
Internal size-recursive canonical truth lemma from:
- canonical neg/imp counterexample obligations, and
- canonical `pi` generalization.

This is the core internal artifact for quantifier truth: no external quantifier oracle is needed.
-/
theorem canonical_truth_lt_of_negImp_and_piGeneralization
    [HasCanonicalNegImpExtensions σ κ]
    [HasCanonicalPiGeneralization σ κ] :
    ∀ (n : Nat) (w : World σ κ) (ψ : FormulaH σ κ),
      Syntax.Henkin.fSize (σ := σ) (κ := κ) ψ < n →
        (HeytingLean.Noneism.KripkeFOH.Forces
            (M := model (σ := σ) (κ := κ))
            idVarValuation idParamInterp w ψ ↔
          ψ ∈ w.carrier) := by
  intro n
  induction n with
  | zero =>
      intro w ψ hlt
      exact (Nat.not_lt_zero _ hlt).elim
  | succ n ih =>
      intro w ψ hlt
      have hψLe : Syntax.Henkin.fSize (σ := σ) (κ := κ) ψ ≤ n :=
        Nat.lt_succ_iff.mp hlt
      have hTruthLt :
          ∀ ψ' : FormulaH σ κ,
            Syntax.Henkin.fSize (σ := σ) (κ := κ) ψ' <
                Syntax.Henkin.fSize (σ := σ) (κ := κ) ψ →
              (HeytingLean.Noneism.KripkeFOH.Forces
                  (M := model (σ := σ) (κ := κ))
                  idVarValuation idParamInterp w ψ' ↔
                ψ' ∈ w.carrier) := by
        intro ψ' hlt'
        exact ih w ψ' (Nat.lt_of_lt_of_le hlt' hψLe)
      have hTruthLtExt :
          ∀ v : World σ κ, w ≤ v →
            ∀ ψ' : FormulaH σ κ,
              Syntax.Henkin.fSize (σ := σ) (κ := κ) ψ' <
                  Syntax.Henkin.fSize (σ := σ) (κ := κ) ψ →
                (HeytingLean.Noneism.KripkeFOH.Forces
                    (M := model (σ := σ) (κ := κ))
                    idVarValuation idParamInterp v ψ' ↔
                  ψ' ∈ v.carrier) := by
        intro v _hwv ψ' hlt'
        exact ih v ψ' (Nat.lt_of_lt_of_le hlt' hψLe)
      cases ψ with
      | top =>
          constructor
          · intro _hTop
            have hDerTop : DerivableH (σ := σ) (κ := κ) w.carrier (.top : FormulaH σ κ) := by
              refine ⟨[], ?_, NDH.Derives.topI⟩
              intro θ hθ
              cases hθ
            exact w.closed _ hDerTop
          · intro _hMem
            simp [HeytingLean.Noneism.KripkeFOH.Forces]
      | bot =>
          constructor
          · intro hBot
            cases hBot
          · intro hMem
            exact False.elim (w.consistent (derivableH_of_mem (σ := σ) (κ := κ) hMem))
      | pred p args =>
          exact CanonicalH.forces_pred_iff_mem (σ := σ) (κ := κ) (w := w) (p := p) (args := args)
      | eExists t =>
          exact CanonicalH.forces_eExists_iff_mem (σ := σ) (κ := κ) (w := w) (t := t)
      | not φ =>
          constructor
          · intro hForce
            by_contra hNotMem
            rcases HasCanonicalNegImpExtensions.not_counterexample
              (σ := σ) (κ := κ) (w := w) (φ := φ) hNotMem with
              ⟨v, hwv, hφMem⟩
            have hφForce :
                HeytingLean.Noneism.KripkeFOH.Forces
                  (M := model (σ := σ) (κ := κ))
                  idVarValuation idParamInterp v φ :=
              ((hTruthLtExt v hwv φ (by simp [Syntax.Henkin.fSize])).2 hφMem)
            exact hForce v hwv hφForce
          · intro hNotMem v hwv hφForce
            have hNotMemV : (.not φ : FormulaH σ κ) ∈ v.carrier := hwv hNotMem
            have hφMemV : φ ∈ v.carrier :=
              ((hTruthLtExt v hwv φ (by simp [Syntax.Henkin.fSize])).1 hφForce)
            have hBotDerV : DerivableH (σ := σ) (κ := κ) v.carrier (.bot : FormulaH σ κ) := by
              refine ⟨[.not φ, φ], ?_, ?_⟩
              · intro θ hθ
                simp at hθ
                rcases hθ with rfl | rfl
                · exact hNotMemV
                · exact hφMemV
              ·
                have hNot' : NDH.Derives (σ := σ) (κ := κ) [.not φ, φ] (.not φ) :=
                  NDH.Derives.hyp (by simp)
                have hφ' : NDH.Derives (σ := σ) (κ := κ) [.not φ, φ] φ :=
                  NDH.Derives.hyp (by simp)
                exact NDH.Derives.notE hNot' hφ'
            exact v.consistent hBotDerV
      | and φ χ =>
          have hφLt :
              Syntax.Henkin.fSize (σ := σ) (κ := κ) φ <
                Syntax.Henkin.fSize (σ := σ) (κ := κ) (.and φ χ) := by
            have h :
                Syntax.Henkin.fSize (σ := σ) (κ := κ) φ <
                  Syntax.Henkin.fSize (σ := σ) (κ := κ) φ +
                    (Syntax.Henkin.fSize (σ := σ) (κ := κ) χ + 1) :=
              Nat.lt_add_of_pos_right (Nat.succ_pos _)
            simpa [Syntax.Henkin.fSize, Nat.add_assoc] using h
          have hχLt :
              Syntax.Henkin.fSize (σ := σ) (κ := κ) χ <
                Syntax.Henkin.fSize (σ := σ) (κ := κ) (.and φ χ) := by
            have h :
                Syntax.Henkin.fSize (σ := σ) (κ := κ) χ <
                  Syntax.Henkin.fSize (σ := σ) (κ := κ) χ +
                    (Syntax.Henkin.fSize (σ := σ) (κ := κ) φ + 1) :=
              Nat.lt_add_of_pos_right (Nat.succ_pos _)
            simpa [Syntax.Henkin.fSize, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
          constructor
          · intro hForce
            have hφMem : φ ∈ w.carrier :=
              (hTruthLt φ hφLt).1 hForce.1
            have hχMem : χ ∈ w.carrier :=
              (hTruthLt χ hχLt).1 hForce.2
            have hDerAnd : DerivableH (σ := σ) (κ := κ) w.carrier (.and φ χ) := by
              refine ⟨[φ, χ], ?_, ?_⟩
              · intro θ hθ
                simp at hθ
                rcases hθ with rfl | rfl
                · exact hφMem
                · exact hχMem
              ·
                have hφ' : NDH.Derives (σ := σ) (κ := κ) [φ, χ] φ :=
                  NDH.Derives.hyp (by simp)
                have hχ' : NDH.Derives (σ := σ) (κ := κ) [φ, χ] χ :=
                  NDH.Derives.hyp (by simp)
                exact NDH.Derives.andI hφ' hχ'
            exact w.closed _ hDerAnd
          · intro hAndMem
            have hφMem : φ ∈ w.carrier := by
              rcases derivableH_of_mem (σ := σ) (κ := κ) hAndMem with ⟨Γ, hΓ, hDer⟩
              exact w.closed _ ⟨Γ, hΓ, NDH.Derives.andEL hDer⟩
            have hχMem : χ ∈ w.carrier := by
              rcases derivableH_of_mem (σ := σ) (κ := κ) hAndMem with ⟨Γ, hΓ, hDer⟩
              exact w.closed _ ⟨Γ, hΓ, NDH.Derives.andER hDer⟩
            exact And.intro
              ((hTruthLt φ hφLt).2 hφMem)
              ((hTruthLt χ hχLt).2 hχMem)
      | or φ χ =>
          have hφLt :
              Syntax.Henkin.fSize (σ := σ) (κ := κ) φ <
                Syntax.Henkin.fSize (σ := σ) (κ := κ) (.or φ χ) := by
            have h :
                Syntax.Henkin.fSize (σ := σ) (κ := κ) φ <
                  Syntax.Henkin.fSize (σ := σ) (κ := κ) φ +
                    (Syntax.Henkin.fSize (σ := σ) (κ := κ) χ + 1) :=
              Nat.lt_add_of_pos_right (Nat.succ_pos _)
            simpa [Syntax.Henkin.fSize, Nat.add_assoc] using h
          have hχLt :
              Syntax.Henkin.fSize (σ := σ) (κ := κ) χ <
                Syntax.Henkin.fSize (σ := σ) (κ := κ) (.or φ χ) := by
            have h :
                Syntax.Henkin.fSize (σ := σ) (κ := κ) χ <
                  Syntax.Henkin.fSize (σ := σ) (κ := κ) χ +
                    (Syntax.Henkin.fSize (σ := σ) (κ := κ) φ + 1) :=
              Nat.lt_add_of_pos_right (Nat.succ_pos _)
            simpa [Syntax.Henkin.fSize, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
          constructor
          · intro hForce
            cases hForce with
            | inl hφForce =>
                have hφMem : φ ∈ w.carrier :=
                  (hTruthLt φ hφLt).1 hφForce
                have hDer : DerivableH (σ := σ) (κ := κ) w.carrier (.or φ χ) := by
                  refine ⟨[φ], ?_, ?_⟩
                  · intro θ hθ
                    simp at hθ
                    subst hθ
                    exact hφMem
                  ·
                    have hφ' : NDH.Derives (σ := σ) (κ := κ) [φ] φ :=
                      NDH.Derives.hyp (by simp)
                    exact NDH.Derives.orIL hφ'
                exact w.closed _ hDer
            | inr hχForce =>
                have hχMem : χ ∈ w.carrier :=
                  (hTruthLt χ hχLt).1 hχForce
                have hDer : DerivableH (σ := σ) (κ := κ) w.carrier (.or φ χ) := by
                  refine ⟨[χ], ?_, ?_⟩
                  · intro θ hθ
                    simp at hθ
                    subst hθ
                    exact hχMem
                  ·
                    have hχ' : NDH.Derives (σ := σ) (κ := κ) [χ] χ :=
                      NDH.Derives.hyp (by simp)
                    exact NDH.Derives.orIR hχ'
                exact w.closed _ hDer
          · intro hOrMem
            rcases w.prime φ χ hOrMem with hφMem | hχMem
            · exact Or.inl ((hTruthLt φ hφLt).2 hφMem)
            · exact Or.inr ((hTruthLt χ hχLt).2 hχMem)
      | imp φ χ =>
          have hφLt :
              Syntax.Henkin.fSize (σ := σ) (κ := κ) φ <
                Syntax.Henkin.fSize (σ := σ) (κ := κ) (.imp φ χ) := by
            have h :
                Syntax.Henkin.fSize (σ := σ) (κ := κ) φ <
                  Syntax.Henkin.fSize (σ := σ) (κ := κ) φ +
                    (Syntax.Henkin.fSize (σ := σ) (κ := κ) χ + 1) :=
              Nat.lt_add_of_pos_right (Nat.succ_pos _)
            simpa [Syntax.Henkin.fSize, Nat.add_assoc] using h
          have hχLt :
              Syntax.Henkin.fSize (σ := σ) (κ := κ) χ <
                Syntax.Henkin.fSize (σ := σ) (κ := κ) (.imp φ χ) := by
            have h :
                Syntax.Henkin.fSize (σ := σ) (κ := κ) χ <
                  Syntax.Henkin.fSize (σ := σ) (κ := κ) χ +
                    (Syntax.Henkin.fSize (σ := σ) (κ := κ) φ + 1) :=
              Nat.lt_add_of_pos_right (Nat.succ_pos _)
            simpa [Syntax.Henkin.fSize, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
          constructor
          · intro hForce
            by_contra hImpMem
            rcases HasCanonicalNegImpExtensions.imp_counterexample
              (σ := σ) (κ := κ) (w := w) (φ := φ) (ψ := χ) hImpMem with
              ⟨v, hwv, hφMem, hχNotMem⟩
            have hφForce :
                HeytingLean.Noneism.KripkeFOH.Forces
                  (M := model (σ := σ) (κ := κ))
                  idVarValuation idParamInterp v φ :=
              ((hTruthLtExt v hwv φ hφLt).2 hφMem)
            have hχForce :
                HeytingLean.Noneism.KripkeFOH.Forces
                  (M := model (σ := σ) (κ := κ))
                  idVarValuation idParamInterp v χ :=
              hForce v hwv hφForce
            exact hχNotMem ((hTruthLtExt v hwv χ hχLt).1 hχForce)
          · intro hImpMem v hwv hφForce
            have hImpMemV : (.imp φ χ : FormulaH σ κ) ∈ v.carrier := hwv hImpMem
            have hφMemV : φ ∈ v.carrier :=
              ((hTruthLtExt v hwv φ hφLt).1 hφForce)
            have hχDer : DerivableH (σ := σ) (κ := κ) v.carrier χ := by
              refine ⟨[.imp φ χ, φ], ?_, ?_⟩
              · intro θ hθ
                simp at hθ
                rcases hθ with rfl | rfl
                · exact hImpMemV
                · exact hφMemV
              ·
                have h1 : NDH.Derives (σ := σ) (κ := κ) [.imp φ χ, φ] (.imp φ χ) :=
                  NDH.Derives.hyp (by simp)
                have h2 : NDH.Derives (σ := σ) (κ := κ) [.imp φ χ, φ] φ :=
                  NDH.Derives.hyp (by simp)
                exact NDH.Derives.impE h1 h2
            have hχMemV : χ ∈ v.carrier := v.closed _ hχDer
            exact (hTruthLtExt v hwv χ hχLt).2 hχMemV
      | sigma x φ =>
          exact CanonicalH.canonical_sigma_forces_iff_mem_of_lt
            (σ := σ) (κ := κ) (w := w) (x := x) (φ := φ) hTruthLt
      | pi x φ =>
          exact CanonicalH.canonical_pi_forces_iff_mem_of_lt_and_generalization_on_extensions
            (σ := σ) (κ := κ)
            (w := w) (x := x) (φ := φ)
            (hTruthLt := by
              intro v hwv ψ' hlt'
              exact hTruthLtExt v hwv ψ' hlt')
            (hPiGeneralize := by
              intro v _hwv hAllInst
              exact HasCanonicalPiGeneralization.pi_generalize (σ := σ) (κ := κ) v x φ hAllInst)

set_option linter.unnecessarySimpa true

instance (priority := 94)
    hasCanonicalTruthBySize_of_negImp_and_piGeneralization
    [HasCanonicalNegImpExtensions σ κ]
    [HasCanonicalPiGeneralization σ κ] :
    HasCanonicalTruthBySize σ κ where
  truth_lt := by
    intro n w ψ hlt
    exact canonical_truth_lt_of_negImp_and_piGeneralization
      (σ := σ) (κ := κ) n w ψ hlt

instance (priority := 95)
    hasCanonicalQuantifierTruth_of_piGeneralization_and_truthBySize
    [HasCanonicalPiGeneralization σ κ]
    [HasCanonicalTruthBySize σ κ] :
    HasCanonicalQuantifierTruth σ κ where
  sigma_forces_iff_mem := by
    intro w x φ
    exact CanonicalH.canonical_sigma_forces_iff_mem_of_lt
      (σ := σ) (κ := κ) (w := w) (x := x) (φ := φ)
      (hTruthLt := by
        intro ψ hlt
        exact HasCanonicalTruthBySize.truth_lt
          (σ := σ) (κ := κ)
          (n := Syntax.Henkin.fSize (σ := σ) (κ := κ) (.sigma x φ))
          (w := w) (ψ := ψ) hlt)
  pi_forces_iff_mem := by
    intro w x φ
    exact CanonicalH.canonical_pi_forces_iff_mem_of_lt_and_generalization_on_extensions
      (σ := σ) (κ := κ) (w := w) (x := x) (φ := φ)
      (hTruthLt := by
        intro v _hwv ψ hlt
        exact HasCanonicalTruthBySize.truth_lt
          (σ := σ) (κ := κ)
          (n := Syntax.Henkin.fSize (σ := σ) (κ := κ) (.pi x φ))
          (w := v) (ψ := ψ) hlt)
      (hPiGeneralize := by
        intro v _hwv hAllInst
        exact HasCanonicalPiGeneralization.pi_generalize (σ := σ) (κ := κ) v x φ hAllInst)

/--
Canonical truth lemma for `FormulaH` from propositional counterexample obligations
plus quantifier-truth obligations.
-/
theorem truth_iff_mem_of_obligations
    [HasCanonicalNegImpExtensions σ κ]
    [HasCanonicalQuantifierTruth σ κ] :
    ∀ (w : World σ κ) (ψ : FormulaH σ κ),
      HeytingLean.Noneism.KripkeFOH.Forces
        (M := model (σ := σ) (κ := κ))
        idVarValuation
        idParamInterp
        w ψ ↔
      ψ ∈ w.carrier := by
  intro w ψ
  induction ψ generalizing w with
  | top =>
      constructor
      · intro _hTop
        have hDerTop : DerivableH (σ := σ) (κ := κ) w.carrier (.top : FormulaH σ κ) := by
          refine ⟨[], ?_, NDH.Derives.topI⟩
          intro θ hθ
          cases hθ
        exact w.closed _ hDerTop
      · intro _hMem
        simp [HeytingLean.Noneism.KripkeFOH.Forces]
  | bot =>
      constructor
      · intro hBot
        cases hBot
      · intro hMem
        exact False.elim (w.consistent (derivableH_of_mem (σ := σ) (κ := κ) hMem))
  | pred p args =>
      exact CanonicalH.forces_pred_iff_mem (σ := σ) (κ := κ) (w := w) (p := p) (args := args)
  | eExists t =>
      exact CanonicalH.forces_eExists_iff_mem (σ := σ) (κ := κ) (w := w) (t := t)
  | not φ ih =>
      constructor
      · intro hForce
        by_contra hNotMem
        rcases HasCanonicalNegImpExtensions.not_counterexample
          (σ := σ) (κ := κ) (w := w) (φ := φ) hNotMem with
          ⟨v, hwv, hφMem⟩
        have hφForce :
            HeytingLean.Noneism.KripkeFOH.Forces
              (M := model (σ := σ) (κ := κ))
              idVarValuation idParamInterp v φ := (ih v).2 hφMem
        exact hForce v hwv hφForce
      · intro hNotMem v hwv hφForce
        have hNotMemV : (.not φ : FormulaH σ κ) ∈ v.carrier := hwv hNotMem
        have hφMemV : φ ∈ v.carrier := (ih v).1 hφForce
        have hBotDerV : DerivableH (σ := σ) (κ := κ) v.carrier (.bot : FormulaH σ κ) := by
          refine ⟨[.not φ, φ], ?_, ?_⟩
          · intro θ hθ
            simp at hθ
            rcases hθ with rfl | rfl
            · exact hNotMemV
            · exact hφMemV
          ·
            have hNot' : NDH.Derives (σ := σ) (κ := κ) [.not φ, φ] (.not φ) :=
              NDH.Derives.hyp (by simp)
            have hφ' : NDH.Derives (σ := σ) (κ := κ) [.not φ, φ] φ :=
              NDH.Derives.hyp (by simp)
            exact NDH.Derives.notE hNot' hφ'
        exact v.consistent hBotDerV
  | and φ ψ ihφ ihψ =>
      constructor
      · intro hAnd
        have hφMem : φ ∈ w.carrier := (ihφ w).1 hAnd.1
        have hψMem : ψ ∈ w.carrier := (ihψ w).1 hAnd.2
        have hDerAnd : DerivableH (σ := σ) (κ := κ) w.carrier (.and φ ψ) := by
          refine ⟨[φ, ψ], ?_, ?_⟩
          · intro θ hθ
            simp at hθ
            rcases hθ with rfl | rfl
            · exact hφMem
            · exact hψMem
          ·
            have hφ' : NDH.Derives (σ := σ) (κ := κ) [φ, ψ] φ :=
              NDH.Derives.hyp (by simp)
            have hψ' : NDH.Derives (σ := σ) (κ := κ) [φ, ψ] ψ :=
              NDH.Derives.hyp (by simp)
            exact NDH.Derives.andI hφ' hψ'
        exact w.closed _ hDerAnd
      · intro hAndMem
        have hφMem : φ ∈ w.carrier := by
          rcases derivableH_of_mem (σ := σ) (κ := κ) hAndMem with ⟨Γ, hΓ, hDer⟩
          exact w.closed _ ⟨Γ, hΓ, NDH.Derives.andEL hDer⟩
        have hψMem : ψ ∈ w.carrier := by
          rcases derivableH_of_mem (σ := σ) (κ := κ) hAndMem with ⟨Γ, hΓ, hDer⟩
          exact w.closed _ ⟨Γ, hΓ, NDH.Derives.andER hDer⟩
        exact And.intro ((ihφ w).2 hφMem) ((ihψ w).2 hψMem)
  | or φ ψ ihφ ihψ =>
      constructor
      · intro hOr
        cases hOr with
        | inl hφForce =>
            have hφMem : φ ∈ w.carrier := (ihφ w).1 hφForce
            have hDer : DerivableH (σ := σ) (κ := κ) w.carrier (.or φ ψ) := by
              refine ⟨[φ], ?_, ?_⟩
              · intro θ hθ
                simp at hθ
                subst hθ
                exact hφMem
              ·
                have hφ' : NDH.Derives (σ := σ) (κ := κ) [φ] φ :=
                  NDH.Derives.hyp (by simp)
                exact NDH.Derives.orIL hφ'
            exact w.closed _ hDer
        | inr hψForce =>
            have hψMem : ψ ∈ w.carrier := (ihψ w).1 hψForce
            have hDer : DerivableH (σ := σ) (κ := κ) w.carrier (.or φ ψ) := by
              refine ⟨[ψ], ?_, ?_⟩
              · intro θ hθ
                simp at hθ
                subst hθ
                exact hψMem
              ·
                have hψ' : NDH.Derives (σ := σ) (κ := κ) [ψ] ψ :=
                  NDH.Derives.hyp (by simp)
                exact NDH.Derives.orIR hψ'
            exact w.closed _ hDer
      · intro hOrMem
        rcases w.prime φ ψ hOrMem with hφMem | hψMem
        · exact Or.inl ((ihφ w).2 hφMem)
        · exact Or.inr ((ihψ w).2 hψMem)
  | imp φ ψ ihφ ihψ =>
      constructor
      · intro hForce
        by_contra hImpMem
        rcases HasCanonicalNegImpExtensions.imp_counterexample
          (σ := σ) (κ := κ) (w := w) (φ := φ) (ψ := ψ) hImpMem with
          ⟨v, hwv, hφMem, hψNotMem⟩
        have hφForce :
            HeytingLean.Noneism.KripkeFOH.Forces
              (M := model (σ := σ) (κ := κ))
              idVarValuation idParamInterp v φ := (ihφ v).2 hφMem
        have hψForce :
            HeytingLean.Noneism.KripkeFOH.Forces
              (M := model (σ := σ) (κ := κ))
              idVarValuation idParamInterp v ψ := hForce v hwv hφForce
        exact hψNotMem ((ihψ v).1 hψForce)
      · intro hImpMem v hwv hφForce
        have hImpMemV : (.imp φ ψ : FormulaH σ κ) ∈ v.carrier := hwv hImpMem
        have hφMemV : φ ∈ v.carrier := (ihφ v).1 hφForce
        have hψDer : DerivableH (σ := σ) (κ := κ) v.carrier ψ := by
          refine ⟨[.imp φ ψ, φ], ?_, ?_⟩
          · intro θ hθ
            simp at hθ
            rcases hθ with rfl | rfl
            · exact hImpMemV
            · exact hφMemV
          ·
            have h1 : NDH.Derives (σ := σ) (κ := κ) [.imp φ ψ, φ] (.imp φ ψ) :=
              NDH.Derives.hyp (by simp)
            have h2 : NDH.Derives (σ := σ) (κ := κ) [.imp φ ψ, φ] φ :=
              NDH.Derives.hyp (by simp)
            exact NDH.Derives.impE h1 h2
        have hψMemV : ψ ∈ v.carrier := v.closed _ hψDer
        exact (ihψ v).2 hψMemV
  | sigma x φ ih =>
      exact HasCanonicalQuantifierTruth.sigma_forces_iff_mem
        (σ := σ) (κ := κ) w x φ
  | pi x φ ih =>
      exact HasCanonicalQuantifierTruth.pi_forces_iff_mem
        (σ := σ) (κ := κ) w x φ

instance (priority := 100)
    hasTruthLemma_of_obligations
    [HasCanonicalNegImpExtensions σ κ]
    [HasCanonicalQuantifierTruth σ κ] :
    HasTruthLemma σ κ where
  truth_iff_mem := by
    intro w ψ
    exact truth_iff_mem_of_obligations
      (σ := σ) (κ := κ) w ψ

/--
Internal Henkin countermodel artifact (standalone, not routed through base FO wrappers).
-/
class HasInternalCountermodel (σ : Type) (κ : Type) : Prop where
  countermodel :
    ∀ {Γ : List (FormulaH σ κ)} {φ : FormulaH σ κ},
      ¬ NDH.Derives (σ := σ) (κ := κ) Γ φ →
        ∃ w : World σ κ,
          (∀ ψ ∈ Γ,
            HeytingLean.Noneism.KripkeFOH.Forces
              (M := model (σ := σ) (κ := κ))
              idVarValuation
              idParamInterp
              w ψ) ∧
          ¬ HeytingLean.Noneism.KripkeFOH.Forces
            (M := model (σ := σ) (κ := κ))
            idVarValuation
            idParamInterp
            w φ

instance (priority := 100)
    hasInternalCountermodel_of_extension_truth
    [HasExtensionConstruction σ κ]
    [HasTruthLemma σ κ] :
    HasInternalCountermodel σ κ where
  countermodel := by
    intro Γ φ hNotDer
    exact countermodel_of_extension_and_truth
      (σ := σ) (κ := κ)
      (Γ := Γ) (φ := φ)
      (HasExtensionConstruction.extend_avoid (σ := σ) (κ := κ))
      (HasTruthLemma.truth_iff_mem (σ := σ) (κ := κ))
      hNotDer

end InternalH

end HenkinCompleteness
end Noneism
end HeytingLean
