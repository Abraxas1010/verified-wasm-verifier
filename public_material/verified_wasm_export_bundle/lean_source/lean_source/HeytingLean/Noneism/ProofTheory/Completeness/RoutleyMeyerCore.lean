import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Zorn
import HeytingLean.Noneism.ProofTheory.NDRMSyntax
import HeytingLean.Noneism.Semantics.KripkeProp

namespace HeytingLean
namespace Noneism
namespace RM

open scoped Classical

open Noneism Formula

/-- Set-level derivability via finite core derivations. -/
def Derivable {σ : Type} (T : Set (Formula σ)) (φ : Formula σ) : Prop :=
  ∃ Γ : List (Formula σ), (∀ ψ ∈ Γ, ψ ∈ T) ∧ NDRMSyntax.DerivesCore Γ φ

/-- A set is core-consistent when `⊥` is not derivable from it. -/
def Consistent {σ : Type} (T : Set (Formula σ)) : Prop :=
  ¬ Derivable T (.bot : Formula σ)

/--
Prime-theory package used by RM canonical constructions.

This version is paraconsistency-friendly: no global consistency field is required.
-/
structure PrimeTheory (σ : Type) where
  carrier : Set (Formula σ)
  consistent : Consistent carrier
  closed  : ∀ φ : Formula σ, Derivable carrier φ → φ ∈ carrier
  prime   : ∀ φ ψ : Formula σ, (.or φ ψ) ∈ carrier → φ ∈ carrier ∨ ψ ∈ carrier

lemma derivable_of_derivesCore {σ : Type} {T : Set (Formula σ)}
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, ψ ∈ T)
    (hDer : NDRMSyntax.DerivesCore Γ φ) :
    Derivable T φ :=
  ⟨Γ, hΓ, hDer⟩

lemma core_weaken {σ : Type} {Γ Δ : List (Formula σ)} {φ : Formula σ}
    (hDer : NDRMSyntax.DerivesCore Γ φ) (hSub : Γ ⊆ Δ) :
    NDRMSyntax.DerivesCore Δ φ := by
  have hEmbSub : NDRM.embedAtZero Γ ⊆ NDRM.embedAtZero Δ := by
    intro a ha
    rcases List.mem_map.1 ha with ⟨ψ, hψΓ, rfl⟩
    exact List.mem_map.2 ⟨ψ, hSub hψΓ, rfl⟩
  exact NDRMSyntax.DerivesL.wk hDer hEmbSub

lemma derivable_of_mem {σ : Type} {T : Set (Formula σ)} {φ : Formula σ}
    (hφ : φ ∈ T) :
    Derivable T φ := by
  refine ⟨[φ], ?_, ?_⟩
  · intro ψ hψ
    simp at hψ
    subst hψ
    exact hφ
  · simpa [NDRMSyntax.DerivesCore, NDRM.embedAtZero] using
      (NDRMSyntax.DerivesL.hyp (Γ := [NDRM.Judgment.frm 0 φ]) (j := NDRM.Judgment.frm 0 φ) (by simp))

lemma Derivable.mono {σ : Type} {T U : Set (Formula σ)} {φ : Formula σ}
    (hTU : T ⊆ U) :
    Derivable T φ → Derivable U φ := by
  rintro ⟨Γ, hΓ, hDer⟩
  refine ⟨Γ, ?_, hDer⟩
  intro ψ hψ
  exact hTU (hΓ ψ hψ)

lemma derivable_of_derivable_bot {σ : Type} {T : Set (Formula σ)} {φ : Formula σ} :
    Derivable T (.bot : Formula σ) → Derivable T φ := by
  rintro ⟨Γ, hΓ, hBot⟩
  exact ⟨Γ, hΓ, NDRMSyntax.DerivesL.botE hBot⟩

namespace PrimeTheory

variable {σ : Type} (w : PrimeTheory σ)

lemma bot_not_mem : (.bot : Formula σ) ∉ w.carrier := by
  intro hBot
  exact w.consistent (derivable_of_mem (T := w.carrier) hBot)

lemma top_mem : (.top : Formula σ) ∈ w.carrier := by
  have hDerTop : Derivable w.carrier (.top : Formula σ) := by
    refine ⟨[], ?_, ?_⟩
    · intro ψ hψ
      cases hψ
    ·
      simpa [NDRMSyntax.DerivesCore, NDRM.embedAtZero] using
        (NDRMSyntax.DerivesL.topI (Γ := []) (w := 0))
  exact w.closed _ hDerTop

lemma and_mem_iff (φ ψ : Formula σ) :
    (.and φ ψ) ∈ w.carrier ↔ φ ∈ w.carrier ∧ ψ ∈ w.carrier := by
  constructor
  · intro hAnd
    have hDerAnd : Derivable w.carrier (.and φ ψ) :=
      derivable_of_mem (T := w.carrier) hAnd
    have hDerφ : Derivable w.carrier φ := by
      rcases hDerAnd with ⟨Γ, hΓ, hDer⟩
      exact ⟨Γ, hΓ, NDRMSyntax.DerivesL.andEL hDer⟩
    have hDerψ : Derivable w.carrier ψ := by
      rcases hDerAnd with ⟨Γ, hΓ, hDer⟩
      exact ⟨Γ, hΓ, NDRMSyntax.DerivesL.andER hDer⟩
    exact ⟨w.closed _ hDerφ, w.closed _ hDerψ⟩
  · rintro ⟨hφ, hψ⟩
    have hDerAnd : Derivable w.carrier (.and φ ψ) := by
      refine ⟨[φ, ψ], ?_, ?_⟩
      · intro θ hθ
        simp at hθ
        rcases hθ with rfl | rfl
        · exact hφ
        · exact hψ
      ·
        have hL :
            NDRMSyntax.DerivesL
              (NDRM.embedAtZero [φ, ψ])
              (.frm 0 φ) :=
          NDRMSyntax.DerivesL.hyp (by simp [NDRM.embedAtZero])
        have hR :
            NDRMSyntax.DerivesL
              (NDRM.embedAtZero [φ, ψ])
              (.frm 0 ψ) :=
          NDRMSyntax.DerivesL.hyp (by simp [NDRM.embedAtZero])
        exact NDRMSyntax.DerivesL.andI hL hR
    exact w.closed _ hDerAnd

lemma or_mem_of_left {φ ψ : Formula σ} (hφ : φ ∈ w.carrier) :
    (.or φ ψ) ∈ w.carrier := by
  have hDer : Derivable w.carrier (.or φ ψ) := by
    refine ⟨[φ], ?_, ?_⟩
    · intro θ hθ
      simp at hθ
      subst hθ
      exact hφ
    ·
      have hL :
          NDRMSyntax.DerivesL
            (NDRM.embedAtZero [φ])
            (.frm 0 φ) :=
        NDRMSyntax.DerivesL.hyp (by simp [NDRM.embedAtZero])
      exact NDRMSyntax.DerivesL.orIL hL
  exact w.closed _ hDer

lemma or_mem_of_right {φ ψ : Formula σ} (hψ : ψ ∈ w.carrier) :
    (.or φ ψ) ∈ w.carrier := by
  have hDer : Derivable w.carrier (.or φ ψ) := by
    refine ⟨[ψ], ?_, ?_⟩
    · intro θ hθ
      simp at hθ
      subst hθ
      exact hψ
    ·
      have hR :
          NDRMSyntax.DerivesL
            (NDRM.embedAtZero [ψ])
            (.frm 0 ψ) :=
        NDRMSyntax.DerivesL.hyp (by simp [NDRM.embedAtZero])
      exact NDRMSyntax.DerivesL.orIR hR
  exact w.closed _ hDer

lemma or_mem_iff (φ ψ : Formula σ) :
    (.or φ ψ) ∈ w.carrier ↔ φ ∈ w.carrier ∨ ψ ∈ w.carrier := by
  constructor
  · intro hOr
    exact w.prime φ ψ hOr
  · intro h
    cases h with
    | inl hφ => exact or_mem_of_left (w := w) hφ
    | inr hψ => exact or_mem_of_right (w := w) hψ

end PrimeTheory

/-- Canonical RM ternary relation induced by implication-membership behavior. -/
def canonicalRworld {σ : Type} (w u v : PrimeTheory σ) : Prop :=
  ∀ φ ψ : Formula σ,
    KripkeProp.IsProp (σ := σ) φ →
      KripkeProp.IsProp (σ := σ) ψ →
        (.imp φ ψ) ∈ w.carrier →
          φ ∈ u.carrier →
            ψ ∈ v.carrier

/--
Syntactic bridge needed by Lindenbaum maximality arguments:
if `φ` is already derivable from `T`, adding `φ` as an explicit assumption does not
create new derivable formulas.
-/
class HasDerivableInsertElim (σ : Type) : Prop where
  derivable_of_insert :
    ∀ {T : Set (Formula σ)} {φ χ : Formula σ},
      Derivable T φ →
        Derivable (Set.insert φ T) χ →
          Derivable T χ

/--
Case-analysis bridge for disjunction with branch assumptions.
-/
class HasDerivableOrCaseElim (σ : Type) : Prop where
  or_case_elim :
    ∀ {T : Set (Formula σ)} {φ ψ χ : Formula σ},
      Derivable T (.or φ ψ) →
        Derivable (Set.insert φ T) χ →
          Derivable (Set.insert ψ T) χ →
            Derivable T χ

lemma derivable_orIL {σ : Type} {T : Set (Formula σ)} {φ ψ : Formula σ} :
    Derivable T φ → Derivable T (.or φ ψ) := by
  rintro ⟨Γ, hΓ, hDer⟩
  exact ⟨Γ, hΓ, NDRMSyntax.DerivesL.orIL hDer⟩

lemma derivable_orIR {σ : Type} {T : Set (Formula σ)} {φ ψ : Formula σ} :
    Derivable T ψ → Derivable T (.or φ ψ) := by
  rintro ⟨Γ, hΓ, hDer⟩
  exact ⟨Γ, hΓ, NDRMSyntax.DerivesL.orIR hDer⟩

theorem derivable_or_case_elim_core {σ : Type}
    {T : Set (Formula σ)} {φ ψ χ : Formula σ} :
    Derivable T (.or φ ψ) →
      Derivable (Set.insert φ T) χ →
        Derivable (Set.insert ψ T) χ →
          Derivable T χ := by
  classical
  intro hOr hL hR
  rcases hOr with ⟨Γor, hΓor, hDerOr⟩
  rcases hL with ⟨ΓL, hΓL, hDerL⟩
  rcases hR with ⟨ΓR, hΓR, hDerR⟩

  let ΓLF : List (Formula σ) := ΓL.filter (fun a => decide (a ≠ φ))
  let ΓRF : List (Formula σ) := ΓR.filter (fun a => decide (a ≠ ψ))
  let Γ : List (Formula σ) := Γor ++ (ΓLF ++ ΓRF)

  have hΓ : ∀ a ∈ Γ, a ∈ T := by
    intro a ha
    rcases List.mem_append.1 ha with haOr | haTail
    · exact hΓor a haOr
    · rcases List.mem_append.1 haTail with haLF | haRF
      · have haL : a ∈ ΓL := (List.mem_filter.1 haLF).1
        have hneq : a ≠ φ := by
          simpa using (List.mem_filter.1 haLF).2
        rcases hΓL a haL with haEq | haT
        · exact (False.elim (hneq haEq))
        · exact haT
      · have haR : a ∈ ΓR := (List.mem_filter.1 haRF).1
        have hneq : a ≠ ψ := by
          simpa using (List.mem_filter.1 haRF).2
        rcases hΓR a haR with haEq | haT
        · exact (False.elim (hneq haEq))
        · exact haT

  have hSubOr : Γor ⊆ Γ := by
    intro a ha
    exact List.mem_append.2 (Or.inl ha)
  have hDerOrΓ : NDRMSyntax.DerivesCore Γ (.or φ ψ) := core_weaken hDerOr hSubOr

  have hDerLΓ :
      NDRMSyntax.DerivesL (.frm 0 φ :: NDRM.embedAtZero Γ) (.frm 0 χ) := by
    refine NDRMSyntax.DerivesL.wk hDerL ?_
    intro j hj
    rcases List.mem_map.1 hj with ⟨a, ha, rfl⟩
    by_cases haEq : a = φ
    · subst haEq
      exact List.mem_cons.2 (Or.inl rfl)
    · apply List.mem_cons.2 (Or.inr ?_)
      apply List.mem_map.2
      refine ⟨a, ?_, rfl⟩
      apply List.mem_append.2
      exact Or.inr (List.mem_append.2 (Or.inl (List.mem_filter.2 ⟨ha, by simp [haEq]⟩)))

  have hDerRΓ :
      NDRMSyntax.DerivesL (.frm 0 ψ :: NDRM.embedAtZero Γ) (.frm 0 χ) := by
    refine NDRMSyntax.DerivesL.wk hDerR ?_
    intro j hj
    rcases List.mem_map.1 hj with ⟨a, ha, rfl⟩
    by_cases haEq : a = ψ
    · subst haEq
      exact List.mem_cons.2 (Or.inl rfl)
    · apply List.mem_cons.2 (Or.inr ?_)
      apply List.mem_map.2
      refine ⟨a, ?_, rfl⟩
      apply List.mem_append.2
      exact Or.inr (List.mem_append.2 (Or.inr (List.mem_filter.2 ⟨ha, by simp [haEq]⟩)))

  refine ⟨Γ, hΓ, ?_⟩
  exact NDRMSyntax.DerivesL.orE hDerOrΓ hDerLΓ hDerRΓ

instance hasDerivableOrCaseElim_core (σ : Type) : HasDerivableOrCaseElim σ where
  or_case_elim := derivable_or_case_elim_core

theorem derivable_insert_elim_of_or_case {σ : Type} [HasDerivableOrCaseElim σ]
    {T : Set (Formula σ)} {φ χ : Formula σ} :
    Derivable T φ →
      Derivable (Set.insert φ T) χ →
        Derivable T χ := by
  intro hφ hχ
  have hor : Derivable T (.or φ φ) := derivable_orIL (T := T) (φ := φ) (ψ := φ) hφ
  exact HasDerivableOrCaseElim.or_case_elim (σ := σ) (T := T) (φ := φ) (ψ := φ) (χ := χ) hor hχ hχ

instance hasDerivableInsertElim_of_or_case (σ : Type) [HasDerivableOrCaseElim σ] :
    HasDerivableInsertElim σ where
  derivable_of_insert := derivable_insert_elim_of_or_case

namespace Lindenbaum

variable {σ : Type}

/-- Zorn family: core-consistent extensions of `S` that avoid deriving `χ`. -/
def Family (S : Set (Formula σ)) (χ : Formula σ) : Set (Set (Formula σ)) :=
  {T | Consistent T ∧ S ⊆ T ∧ ¬ Derivable T χ}

lemma family_mem_of_base {S : Set (Formula σ)} {χ : Formula σ}
    (hS : Consistent S) (hχ : ¬ Derivable S χ) :
    S ∈ Family (S := S) χ := by
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
    (hcF : c ⊆ Family (S := S) χ)
    (hc : IsChain (· ⊆ ·) c)
    (hcne : c.Nonempty) :
    Set.sUnion c ∈ Family (S := S) χ := by
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
    have htCons : Consistent t := (hcF htC).1
    exact htCons (derivable_of_derivesCore (T := t) (Γ := Γ) (φ := .bot)
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
    have htNo : ¬ Derivable t χ := (hcF htC).2.2
    exact htNo (derivable_of_derivesCore (T := t) (Γ := Γ) (φ := χ)
      (by intro ψ hψ; exact hΓt ψ hψ) hDerχ)

/-- Existence of a maximal element of `Family S χ` extending `S`. -/
lemma exists_maximal (S : Set (Formula σ)) (χ : Formula σ)
    (hS : Consistent S) (hχ : ¬ Derivable S χ) :
    ∃ M : Set (Formula σ), S ⊆ M ∧ Maximal (· ∈ Family (S := S) χ) M := by
  classical
  have hmem : S ∈ Family (S := S) χ := family_mem_of_base (S := S) (χ := χ) hS hχ
  have H :
      ∀ c ⊆ Family (S := S) χ,
        IsChain (· ⊆ ·) c →
          c.Nonempty →
            ∃ ub ∈ Family (S := S) χ, ∀ s ∈ c, s ⊆ ub := by
    intro c hcF hc hcne
    refine ⟨Set.sUnion c, ?_, ?_⟩
    · exact sUnion_mem_family (S := S) (χ := χ) (c := c) hcF hc hcne
    · intro s hs
      exact Set.subset_sUnion_of_mem hs
  rcases zorn_subset_nonempty (Family (S := S) χ) H S hmem with ⟨M, hSM, hMax⟩
  exact ⟨M, hSM, hMax⟩

/--
If `M` is maximal in `Family S χ`, then every formula derivable from `M` is already in `M`.

This is the RM-core analogue of Lindenbaum closure, parameterized by
`HasDerivableInsertElim`.
-/
lemma closed_of_maximal
    {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)}
    (hMF : M ∈ Family (S := S) χ)
    (hMax : Maximal (· ∈ Family (S := S) χ) M) :
    ∀ φ : Formula σ, Derivable M φ → φ ∈ M := by
  classical
  intro φ hDer
  by_contra hmem
  have hSsub : S ⊆ M := hMF.2.1
  have hCons : Consistent M := hMF.1
  have hNoχ : ¬ Derivable M χ := hMF.2.2

  have hConsIns : Consistent (Set.insert φ M) := by
    intro hbot
    have : Derivable M (.bot : Formula σ) :=
      HasDerivableInsertElim.derivable_of_insert (σ := σ) (T := M) (φ := φ) (χ := .bot) hDer hbot
    exact hCons this

  have hNoχIns : ¬ Derivable (Set.insert φ M) χ := by
    intro hχ
    have : Derivable M χ :=
      HasDerivableInsertElim.derivable_of_insert (σ := σ) (T := M) (φ := φ) (χ := χ) hDer hχ
    exact hNoχ this

  have hFamIns : Set.insert φ M ∈ Family (S := S) χ := by
    refine ⟨hConsIns, ?_, hNoχIns⟩
    intro ψ hψ
    exact Or.inr (hSsub hψ)

  have hMSub : M ⊆ Set.insert φ M := by
    intro ψ hψ
    exact Or.inr hψ

  have hEq : Set.insert φ M = M := (hMax.eq_of_subset hFamIns hMSub).symm
  have hφIn : φ ∈ M := by
    have hIns : φ ∈ Set.insert φ M := by exact Or.inl rfl
    simpa [hEq] using hIns
  exact hmem hφIn

end Lindenbaum

/-!
Paraconsistent Lindenbaum route: maximize among extensions that avoid deriving `χ`,
without requiring consistency (`⊥`-avoidance).
-/
namespace LindenbaumAvoid

variable {σ : Type}

def disjList : List (Formula σ) → Formula σ
  | [] => (.bot : Formula σ)
  | φ :: Γ => (.or φ (disjList Γ) : Formula σ)

lemma derivable_disjList_of_mem_singleton
    {χ : Formula σ} {Γ : List (Formula σ)}
    (hχ : χ ∈ Γ) :
    Derivable ({χ} : Set (Formula σ)) (disjList (σ := σ) Γ) := by
  induction Γ with
  | nil =>
      cases hχ
  | cons φ Γ ih =>
      simp at hχ
      rcases hχ with hEq | hTail
      · subst hEq
        exact derivable_orIL (T := ({χ} : Set (Formula σ))) (φ := χ)
          (ψ := disjList (σ := σ) Γ)
          (derivable_of_mem (T := ({χ} : Set (Formula σ))) (by simp))
      · exact derivable_orIR (T := ({χ} : Set (Formula σ))) (φ := φ)
          (ψ := disjList (σ := σ) Γ) (ih hTail)

def Family (S : Set (Formula σ)) (χ : Formula σ) : Set (Set (Formula σ)) :=
  {T | S ⊆ T ∧ ¬ Derivable T χ}

lemma family_mem_of_base {S : Set (Formula σ)} {χ : Formula σ}
    (hχ : ¬ Derivable S χ) :
    S ∈ Family (S := S) χ := by
  refine ⟨?_, hχ⟩
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
    (hcF : c ⊆ Family (S := S) χ)
    (hc : IsChain (· ⊆ ·) c)
    (hcne : c.Nonempty) :
    Set.sUnion c ∈ Family (S := S) χ := by
  classical
  refine ⟨?base, ?notDerivable⟩
  · intro φ hφ
    rcases hcne with ⟨t, htC⟩
    have hSt : S ⊆ t := (hcF htC).1
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
    have htNo : ¬ Derivable t χ := (hcF htC).2
    exact htNo (derivable_of_derivesCore (T := t) (Γ := Γ) (φ := χ)
      (by intro ψ hψ; exact hΓt ψ hψ) hDerχ)

lemma exists_maximal (S : Set (Formula σ)) (χ : Formula σ)
    (hχ : ¬ Derivable S χ) :
    ∃ M : Set (Formula σ), S ⊆ M ∧ Maximal (· ∈ Family (S := S) χ) M := by
  classical
  have hmem : S ∈ Family (S := S) χ := family_mem_of_base (S := S) (χ := χ) hχ
  have H :
      ∀ c ⊆ Family (S := S) χ,
        IsChain (· ⊆ ·) c →
          c.Nonempty →
            ∃ ub ∈ Family (S := S) χ, ∀ s ∈ c, s ⊆ ub := by
    intro c hcF hc hcne
    refine ⟨Set.sUnion c, ?_, ?_⟩
    · exact sUnion_mem_family (S := S) (χ := χ) (c := c) hcF hc hcne
    · intro s hs
      exact Set.subset_sUnion_of_mem hs
  rcases zorn_subset_nonempty (Family (S := S) χ) H S hmem with ⟨M, hSM, hMax⟩
  exact ⟨M, hSM, hMax⟩

lemma closed_of_maximal
    {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)}
    (hMF : M ∈ Family (S := S) χ)
    (hMax : Maximal (· ∈ Family (S := S) χ) M) :
    ∀ φ : Formula σ, Derivable M φ → φ ∈ M := by
  classical
  intro φ hDer
  by_contra hmem
  have hSsub : S ⊆ M := hMF.1
  have hNoχ : ¬ Derivable M χ := hMF.2

  have hNoχIns : ¬ Derivable (Set.insert φ M) χ := by
    intro hχ
    have : Derivable M χ :=
      HasDerivableInsertElim.derivable_of_insert (σ := σ) (T := M) (φ := φ) (χ := χ) hDer hχ
    exact hNoχ this

  have hFamIns : Set.insert φ M ∈ Family (S := S) χ := by
    refine ⟨?_, hNoχIns⟩
    intro ψ hψ
    exact Or.inr (hSsub hψ)

  have hMSub : M ⊆ Set.insert φ M := by
    intro ψ hψ
    exact Or.inr hψ

  have hEq : Set.insert φ M = M := (hMax.eq_of_subset hFamIns hMSub).symm
  have hφIn : φ ∈ M := by
    have hIns : φ ∈ Set.insert φ M := by exact Or.inl rfl
    simpa [hEq] using hIns
  exact hmem hφIn

lemma prime_of_maximal
    {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)}
    (hMF : M ∈ Family (S := S) χ)
    (hMax : Maximal (· ∈ Family (S := S) χ) M)
    (hClosed : ∀ φ : Formula σ, Derivable M φ → φ ∈ M) :
    ∀ φ ψ : Formula σ, (.or φ ψ) ∈ M → φ ∈ M ∨ ψ ∈ M := by
  classical
  intro φ ψ hor
  by_contra hne
  have hφ : φ ∉ M := by
    intro h
    exact hne (Or.inl h)
  have hψ : ψ ∉ M := by
    intro h
    exact hne (Or.inr h)

  have hDerNotMem : ∀ th : Formula σ, th ∉ M → ¬ Derivable M th := by
    intro th hth hDer
    exact hth (hClosed th hDer)

  have hDerIns (th : Formula σ) (hDerNot : ¬ Derivable M th) :
      Derivable (Set.insert th M) χ := by
    by_contra hNo
    have hSsub : S ⊆ M := hMF.1
    have hFamIns : Set.insert th M ∈ Family (S := S) χ := by
      refine ⟨?_, hNo⟩
      intro x hx
      exact Or.inr (hSsub hx)
    have hSub : M ⊆ Set.insert th M := by
      intro x hx
      exact Or.inr hx
    have hEq : Set.insert th M = M := (hMax.eq_of_subset hFamIns hSub).symm
    have hthIn : th ∈ M := by
      have : th ∈ Set.insert th M := Or.inl rfl
      simpa [hEq] using this
    exact hDerNot (derivable_of_mem (T := M) hthIn)

  have hχM : Derivable M χ :=
    HasDerivableOrCaseElim.or_case_elim (σ := σ) (T := M) (φ := φ) (ψ := ψ) (χ := χ)
      (derivable_of_mem (T := M) hor)
      (hDerIns φ (hDerNotMem φ hφ))
      (hDerIns ψ (hDerNotMem ψ hψ))
  exact hMF.2 hχM

theorem exists_primeTheory_avoid
    (S : Set (Formula σ)) (χ : Formula σ)
    (hχ : ¬ Derivable S χ) :
    ∃ W : PrimeTheory σ, S ⊆ W.carrier ∧ χ ∉ W.carrier := by
  classical
  rcases exists_maximal (S := S) (χ := χ) hχ with ⟨M, hSM, hMax⟩
  have hMF : M ∈ Family (S := S) χ := hMax.prop
  have hClosed : ∀ φ : Formula σ, Derivable M φ → φ ∈ M :=
    closed_of_maximal (S := S) (χ := χ) (M := M) hMF hMax
  have hPrime : ∀ φ ψ : Formula σ, (.or φ ψ) ∈ M → φ ∈ M ∨ ψ ∈ M :=
    prime_of_maximal (S := S) (χ := χ) (M := M) hMF hMax hClosed
  have hCons : Consistent M := by
    intro hBot
    exact hMF.2 (derivable_of_derivable_bot (T := M) (φ := χ) hBot)
  have hNotMem : χ ∉ M := by
    intro hMem
    exact hMF.2 (derivable_of_mem (T := M) hMem)
  refine ⟨⟨M, hCons, hClosed, hPrime⟩, hSM, hNotMem⟩

theorem exists_primeTheory_avoid_finset
    (S : Set (Formula σ)) (C : Finset (Formula σ))
    (hDisj : ¬ Derivable S (disjList (σ := σ) C.toList)) :
    ∃ W : PrimeTheory σ, S ⊆ W.carrier ∧ ∀ χ ∈ C, χ ∉ W.carrier := by
  rcases exists_primeTheory_avoid (S := S) (χ := disjList (σ := σ) C.toList) hDisj with
    ⟨W, hS, hNotDisj⟩
  refine ⟨W, hS, ?_⟩
  intro χ hχC hχW
  have hχList : χ ∈ C.toList := Finset.mem_toList.2 hχC
  have hDerSingle :
      Derivable ({χ} : Set (Formula σ)) (disjList (σ := σ) C.toList) :=
    derivable_disjList_of_mem_singleton (σ := σ) hχList
  have hSub : ({χ} : Set (Formula σ)) ⊆ W.carrier := by
    intro θ hθ
    have hEq : θ = χ := by simpa [Set.mem_singleton_iff] using hθ
    subst hEq
    exact hχW
  have hDerW : Derivable W.carrier (disjList (σ := σ) C.toList) :=
    (Derivable.mono (T := ({χ} : Set (Formula σ))) (U := W.carrier) hSub) hDerSingle
  exact hNotDisj (W.closed _ hDerW)

theorem exists_primeTheory_reflect_finset
    (S : Set (Formula σ)) (F : Finset (Formula σ))
    (hDisj :
      ¬ Derivable S
        (disjList (σ := σ) (F.filter (fun χ => χ ∉ S)).toList)) :
    ∃ W : PrimeTheory σ,
      S ⊆ W.carrier ∧
      ∀ χ ∈ F, (χ ∈ W.carrier ↔ χ ∈ S) := by
  let C : Finset (Formula σ) := F.filter (fun χ => χ ∉ S)
  rcases exists_primeTheory_avoid_finset (S := S) (C := C) hDisj with
    ⟨W, hS, hAvoid⟩
  refine ⟨W, hS, ?_⟩
  intro χ hχF
  constructor
  · intro hχW
    by_cases hχS : χ ∈ S
    · exact hχS
    · have hχC : χ ∈ C := by
        exact Finset.mem_filter.2 ⟨hχF, hχS⟩
      exact False.elim (hAvoid χ hχC hχW)
  · intro hχS
    exact hS hχS

/--
Multi-target avoidance family:
extend `S` while avoiding derivability of every formula in `C`.
-/
def FamilySet (S C : Set (Formula σ)) : Set (Set (Formula σ)) :=
  {T | S ⊆ T ∧ ∀ χ ∈ C, ¬ Derivable T χ}

lemma familySet_mem_of_base {S C : Set (Formula σ)}
    (hC : ∀ χ ∈ C, ¬ Derivable S χ) :
    S ∈ FamilySet (S := S) C := by
  refine ⟨?_, ?_⟩
  · intro φ hφ
    exact hφ
  · intro χ hχ
    exact hC χ hχ

lemma sUnion_mem_familySet {S C : Set (Formula σ)}
    {c : Set (Set (Formula σ))}
    (hcF : c ⊆ FamilySet (S := S) C)
    (hc : IsChain (· ⊆ ·) c)
    (hcne : c.Nonempty) :
    Set.sUnion c ∈ FamilySet (S := S) C := by
  classical
  refine ⟨?base, ?avoid⟩
  · intro φ hφ
    rcases hcne with ⟨t, htC⟩
    have hSt : S ⊆ t := (hcF htC).1
    exact Set.subset_sUnion_of_mem htC (hSt hφ)
  · intro χ hχC hDer
    rcases hDer with ⟨Γ, hΓ, hDerχ⟩
    let fs : Finset (Formula σ) := Γ.toFinset
    have hfsfin : (fs : Set (Formula σ)).Finite := fs.finite_toSet
    have hfsSub : (fs : Set (Formula σ)) ⊆ Set.sUnion c := by
      intro θ hθ
      have : θ ∈ Γ := List.mem_toFinset.1 hθ
      exact hΓ θ this
    have hdir : DirectedOn (· ⊆ ·) c := chain_directedOn (hc := hc)
    rcases
        DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion
          (α := Formula σ) (c := c) hcne hdir (s := (fs : Set (Formula σ))) hfsfin hfsSub with
      ⟨t, htC, hfst⟩
    have hΓt : ∀ θ ∈ Γ, θ ∈ t := by
      intro θ hθ
      have : θ ∈ (fs : Set (Formula σ)) := List.mem_toFinset.2 hθ
      exact hfst this
    have htNo : ¬ Derivable t χ := (hcF htC).2 χ hχC
    exact htNo (derivable_of_derivesCore (T := t) (Γ := Γ) (φ := χ)
      (by intro θ hθ; exact hΓt θ hθ) hDerχ)

lemma exists_maximal_set_avoid (S C : Set (Formula σ))
    (hC : ∀ χ ∈ C, ¬ Derivable S χ) :
    ∃ M : Set (Formula σ), S ⊆ M ∧ Maximal (· ∈ FamilySet (S := S) C) M := by
  classical
  have hmem : S ∈ FamilySet (S := S) C := familySet_mem_of_base (S := S) (C := C) hC
  have H :
      ∀ c ⊆ FamilySet (S := S) C,
        IsChain (· ⊆ ·) c →
          c.Nonempty →
            ∃ ub ∈ FamilySet (S := S) C, ∀ s ∈ c, s ⊆ ub := by
    intro c hcF hc hcne
    refine ⟨Set.sUnion c, ?_, ?_⟩
    · exact sUnion_mem_familySet (S := S) (C := C) (c := c) hcF hc hcne
    · intro s hs
      exact Set.subset_sUnion_of_mem hs
  rcases zorn_subset_nonempty (FamilySet (S := S) C) H S hmem with ⟨M, hSM, hMax⟩
  exact ⟨M, hSM, hMax⟩

end LindenbaumAvoid

/--
Interface for a canonical RM model over prime theories with a truth lemma.
-/
class HasPrimeTheoryTruthModel (σ : Type) where
  D          : Type
  model      : RM.Model σ (PrimeTheory σ) D
  valuation  : RM.Valuation D
  truth_lemma :
    ∀ (w : PrimeTheory σ) (φ : Formula σ),
      RM.sat model valuation w φ ↔ φ ∈ w.carrier

/--
Obligation decomposition for building `HasPrimeTheoryTruthModel`.

The easy constructors (`⊤`, `⊥`, `∧`, `∨`) are discharged from `PrimeTheory` structure and
closure lemmas; users only provide the hard semantic bridges.
-/
class HasPrimeTheoryTruthObligations (σ : Type) where
  D                : Type
  model            : RM.Model σ (PrimeTheory σ) D
  valuation        : RM.Valuation D
  pred_iff_mem     : ∀ (w : PrimeTheory σ) (p : σ) (ts : List Noneism.Term),
      RM.sat model valuation w (.pred p ts) ↔ (.pred p ts) ∈ w.carrier
  eExists_iff_mem  : ∀ (w : PrimeTheory σ) (t : Noneism.Term),
      RM.sat model valuation w (.eExists t) ↔ (.eExists t) ∈ w.carrier
  not_iff_mem      : ∀ (w : PrimeTheory σ) (φ : Formula σ),
      RM.sat model valuation w (.not φ) ↔ (.not φ) ∈ w.carrier
  imp_iff_mem      : ∀ (w : PrimeTheory σ) (φ ψ : Formula σ),
      RM.sat model valuation w (.imp φ ψ) ↔ (.imp φ ψ) ∈ w.carrier
  sigma_iff_mem    : ∀ (w : PrimeTheory σ) (x : Noneism.Var) (φ : Formula σ),
      RM.sat model valuation w (.sigma x φ) ↔ (.sigma x φ) ∈ w.carrier
  pi_iff_mem       : ∀ (w : PrimeTheory σ) (x : Noneism.Var) (φ : Formula σ),
      RM.sat model valuation w (.pi x φ) ↔ (.pi x φ) ∈ w.carrier

def primeTruthObligationsOfModel
    (σ : Type) [H : HasPrimeTheoryTruthModel σ] :
    HasPrimeTheoryTruthObligations σ where
  D := H.D
  model := H.model
  valuation := H.valuation
  pred_iff_mem := by
    intro w p ts
    exact H.truth_lemma w (.pred p ts)
  eExists_iff_mem := by
    intro w t
    exact H.truth_lemma w (.eExists t)
  not_iff_mem := by
    intro w φ
    exact H.truth_lemma w (.not φ)
  imp_iff_mem := by
    intro w φ ψ
    exact H.truth_lemma w (.imp φ ψ)
  sigma_iff_mem := by
    intro w x φ
    exact H.truth_lemma w (.sigma x φ)
  pi_iff_mem := by
    intro w x φ
    exact H.truth_lemma w (.pi x φ)

instance hasPrimeTheoryTruthModel_of_obligations
    (σ : Type) [H : HasPrimeTheoryTruthObligations σ] :
    HasPrimeTheoryTruthModel σ where
  D := H.D
  model := H.model
  valuation := H.valuation
  truth_lemma := by
    intro w φ
    induction φ with
    | top =>
        constructor
        · intro _
          exact PrimeTheory.top_mem (w := w)
        · intro _
          trivial
    | bot =>
        constructor
        · intro h
          cases h
        · intro h
          exact (PrimeTheory.bot_not_mem (w := w)) h
    | pred p ts =>
        exact H.pred_iff_mem w p ts
    | eExists t =>
        exact H.eExists_iff_mem w t
    | not φ ih =>
        exact H.not_iff_mem w φ
    | and φ ψ ihφ ihψ =>
        simpa [RM.sat, ihφ, ihψ] using (PrimeTheory.and_mem_iff (w := w) φ ψ).symm
    | or φ ψ ihφ ihψ =>
        simpa [RM.sat, ihφ, ihψ] using (PrimeTheory.or_mem_iff (w := w) φ ψ).symm
    | imp φ ψ ihφ ihψ =>
        exact H.imp_iff_mem w φ ψ
    | sigma x φ ih =>
        exact H.sigma_iff_mem w x φ
    | pi x φ ih =>
        exact H.pi_iff_mem w x φ

namespace CanonicalCandidate

variable {σ : Type}

abbrev D : Type := Noneism.Term

def valuation : RM.Valuation D := fun x => .var x

@[simp] lemma evalTerm_valuation (t : Noneism.Term) :
    RM.evalTerm valuation t = t := by
  cases t
  rfl

def model (starWorld : PrimeTheory σ → PrimeTheory σ)
    (Rworld : PrimeTheory σ → PrimeTheory σ → PrimeTheory σ → Prop) :
    RM.Model σ (PrimeTheory σ) D where
  F := { star := starWorld, R := Rworld }
  interp w p args := (.pred p args : Formula σ) ∈ w.carrier
  existsP w d := (.eExists d : Formula σ) ∈ w.carrier

lemma pred_iff_mem (starWorld : PrimeTheory σ → PrimeTheory σ)
    (Rworld : PrimeTheory σ → PrimeTheory σ → PrimeTheory σ → Prop)
    (w : PrimeTheory σ) (p : σ) (ts : List Noneism.Term) :
    RM.sat (model (σ := σ) starWorld Rworld) valuation w (.pred p ts) ↔
      (.pred p ts : Formula σ) ∈ w.carrier := by
  have hMap : List.map (RM.evalTerm valuation) ts = ts := by
    induction ts with
    | nil => rfl
    | cons t ts ih =>
        simp [evalTerm_valuation, ih]
  simp [RM.sat, model, hMap]

lemma eExists_iff_mem (starWorld : PrimeTheory σ → PrimeTheory σ)
    (Rworld : PrimeTheory σ → PrimeTheory σ → PrimeTheory σ → Prop)
    (w : PrimeTheory σ) (t : Noneism.Term) :
    RM.sat (model (σ := σ) starWorld Rworld) valuation w (.eExists t) ↔
      (.eExists t : Formula σ) ∈ w.carrier := by
  simp [RM.sat, model, evalTerm_valuation]

end CanonicalCandidate

open KripkeProp

/--
Propositional-fragment truth-model interface for RM canonical worlds.
-/
class HasPrimeTheoryTruthModelProp (σ : Type) where
  D                : Type
  model            : RM.Model σ (PrimeTheory σ) D
  valuation        : RM.Valuation D
  truth_lemma_prop :
    ∀ (w : PrimeTheory σ) (φ : Formula σ),
      KripkeProp.IsProp (σ := σ) φ →
        (RM.sat model valuation w φ ↔ φ ∈ w.carrier)

def primeTruthModelPropOfModel
    (σ : Type) [H : HasPrimeTheoryTruthModel σ] :
    HasPrimeTheoryTruthModelProp σ where
  D := H.D
  model := H.model
  valuation := H.valuation
  truth_lemma_prop := by
    intro w φ hφ
    exact H.truth_lemma w φ

instance hasPrimeTheoryTruthModelProp_of_model
    (σ : Type) [HasPrimeTheoryTruthModel σ] :
    HasPrimeTheoryTruthModelProp σ :=
  primeTruthModelPropOfModel σ

/--
FO-lift obligations over an existing proposition-level prime-theory truth model.

This isolates the remaining non-propositional bridge needed to recover
`HasPrimeTheoryTruthObligations` (and thus full `HasPrimeTheoryTruthModel`) from the
proposition lane.
-/
class HasPrimeTheoryNegImpLift (σ : Type) (P : HasPrimeTheoryTruthModelProp σ) where
  not_iff_mem :
    ∀ (w : PrimeTheory σ) (φ : Formula σ),
      RM.sat P.model P.valuation w (.not φ) ↔
        (.not φ) ∈ w.carrier
  imp_iff_mem :
    ∀ (w : PrimeTheory σ) (φ ψ : Formula σ),
      RM.sat P.model P.valuation w (.imp φ ψ) ↔
        (.imp φ ψ) ∈ w.carrier

class HasPrimeTheoryQuantifierLift (σ : Type) (P : HasPrimeTheoryTruthModelProp σ) where
  sigma_iff_mem :
    ∀ (w : PrimeTheory σ) (x : Noneism.Var) (φ : Formula σ),
      RM.sat P.model P.valuation w (.sigma x φ) ↔
        (.sigma x φ) ∈ w.carrier
  pi_iff_mem :
    ∀ (w : PrimeTheory σ) (x : Noneism.Var) (φ : Formula σ),
      RM.sat P.model P.valuation w (.pi x φ) ↔
        (.pi x φ) ∈ w.carrier

class HasPrimeTheoryTruthLift (σ : Type) (P : HasPrimeTheoryTruthModelProp σ)
    extends HasPrimeTheoryNegImpLift σ P, HasPrimeTheoryQuantifierLift σ P

instance hasPrimeTheoryNegImpLift_of_truthLift
    (σ : Type) [P : HasPrimeTheoryTruthModelProp σ] [HasPrimeTheoryTruthLift σ P] :
    HasPrimeTheoryNegImpLift σ P where
  not_iff_mem := (inferInstance : HasPrimeTheoryTruthLift σ P).not_iff_mem
  imp_iff_mem := (inferInstance : HasPrimeTheoryTruthLift σ P).imp_iff_mem

instance hasPrimeTheoryQuantifierLift_of_truthLift
    (σ : Type) [P : HasPrimeTheoryTruthModelProp σ] [HasPrimeTheoryTruthLift σ P] :
    HasPrimeTheoryQuantifierLift σ P where
  sigma_iff_mem := (inferInstance : HasPrimeTheoryTruthLift σ P).sigma_iff_mem
  pi_iff_mem := (inferInstance : HasPrimeTheoryTruthLift σ P).pi_iff_mem

instance hasPrimeTheoryTruthLift_of_split
    (σ : Type) [P : HasPrimeTheoryTruthModelProp σ]
    [HasPrimeTheoryNegImpLift σ P] [HasPrimeTheoryQuantifierLift σ P] :
    HasPrimeTheoryTruthLift σ P where
  not_iff_mem := (inferInstance : HasPrimeTheoryNegImpLift σ P).not_iff_mem
  imp_iff_mem := (inferInstance : HasPrimeTheoryNegImpLift σ P).imp_iff_mem
  sigma_iff_mem := (inferInstance : HasPrimeTheoryQuantifierLift σ P).sigma_iff_mem
  pi_iff_mem := (inferInstance : HasPrimeTheoryQuantifierLift σ P).pi_iff_mem

instance hasPrimeTheoryTruthObligations_of_modelProp_lift
    (σ : Type) [P : HasPrimeTheoryTruthModelProp σ] [HasPrimeTheoryTruthLift σ P] :
    HasPrimeTheoryTruthObligations σ where
  D := P.D
  model := P.model
  valuation := P.valuation
  pred_iff_mem := by
    intro w p ts
    exact P.truth_lemma_prop w (.pred p ts) (KripkeProp.IsProp.pred p ts)
  eExists_iff_mem := by
    intro w t
    exact P.truth_lemma_prop w (.eExists t) (KripkeProp.IsProp.eExists t)
  not_iff_mem := (inferInstance : HasPrimeTheoryTruthLift σ P).not_iff_mem
  imp_iff_mem := (inferInstance : HasPrimeTheoryTruthLift σ P).imp_iff_mem
  sigma_iff_mem := (inferInstance : HasPrimeTheoryTruthLift σ P).sigma_iff_mem
  pi_iff_mem := (inferInstance : HasPrimeTheoryTruthLift σ P).pi_iff_mem

instance hasPrimeTheoryTruthLift_of_model
    (σ : Type) [H : HasPrimeTheoryTruthModel σ] :
    HasPrimeTheoryTruthLift σ (primeTruthModelPropOfModel σ) := by
  refine
    { toHasPrimeTheoryNegImpLift := ?_
      toHasPrimeTheoryQuantifierLift := ?_ }
  · refine
      { not_iff_mem := ?_
        imp_iff_mem := ?_ }
    · intro w φ
      simpa using (H.truth_lemma w (.not φ))
    · intro w φ ψ
      simpa using (H.truth_lemma w (.imp φ ψ))
  · refine
      { sigma_iff_mem := ?_
        pi_iff_mem := ?_ }
    · intro w x φ
      simpa using (H.truth_lemma w (.sigma x φ))
    · intro w x φ
      simpa using (H.truth_lemma w (.pi x φ))

instance hasPrimeTheoryNegImpLift_of_model
    (σ : Type) [H : HasPrimeTheoryTruthModel σ] :
    HasPrimeTheoryNegImpLift σ (primeTruthModelPropOfModel σ) :=
  (inferInstance : HasPrimeTheoryTruthLift σ (primeTruthModelPropOfModel σ)).toHasPrimeTheoryNegImpLift

instance hasPrimeTheoryQuantifierLift_of_model
    (σ : Type) [H : HasPrimeTheoryTruthModel σ] :
    HasPrimeTheoryQuantifierLift σ (primeTruthModelPropOfModel σ) :=
  (inferInstance : HasPrimeTheoryTruthLift σ (primeTruthModelPropOfModel σ)).toHasPrimeTheoryQuantifierLift

theorem primeTruthLift_of_model_explicit
    (σ : Type) [HasPrimeTheoryTruthModel σ] :
    @HasPrimeTheoryTruthLift σ (primeTruthModelPropOfModel σ) := by
  infer_instance

/--
Obligation decomposition for propositional RM canonical truth.

`⊤`, `⊥`, `∧`, `∨` are discharged internally via `PrimeTheory` lemmas.
Users provide only atomic + `¬`/`→` bridges on propositional formulas.
-/
class HasPrimeTheoryTruthObligationsProp (σ : Type) where
  D                : Type
  model            : RM.Model σ (PrimeTheory σ) D
  valuation        : RM.Valuation D
  pred_iff_mem     : ∀ (w : PrimeTheory σ) (p : σ) (ts : List Noneism.Term),
      RM.sat model valuation w (.pred p ts) ↔ (.pred p ts) ∈ w.carrier
  eExists_iff_mem  : ∀ (w : PrimeTheory σ) (t : Noneism.Term),
      RM.sat model valuation w (.eExists t) ↔ (.eExists t) ∈ w.carrier
  not_mem_iff_prop :
    ∀ (w : PrimeTheory σ) (φ : Formula σ),
      KripkeProp.IsProp (σ := σ) φ →
        ((.not φ) ∈ w.carrier ↔ φ ∉ (model.F.star w).carrier)
  imp_mem_iff_prop :
    ∀ (w : PrimeTheory σ) (φ ψ : Formula σ),
      KripkeProp.IsProp (σ := σ) φ →
        KripkeProp.IsProp (σ := σ) ψ →
          ((.imp φ ψ) ∈ w.carrier ↔
            ∀ u v, model.F.R w u v → (φ ∈ u.carrier → ψ ∈ v.carrier))

def primeTruthObligationsPropOfModelProp
    (σ : Type) [H : HasPrimeTheoryTruthModelProp σ] :
    HasPrimeTheoryTruthObligationsProp σ where
  D := H.D
  model := H.model
  valuation := H.valuation
  pred_iff_mem := by
    intro w p ts
    exact H.truth_lemma_prop w (.pred p ts) (KripkeProp.IsProp.pred p ts)
  eExists_iff_mem := by
    intro w t
    exact H.truth_lemma_prop w (.eExists t) (KripkeProp.IsProp.eExists t)
  not_mem_iff_prop := by
    intro w φ hφ
    have hNot := H.truth_lemma_prop w (.not φ) (KripkeProp.IsProp.not hφ)
    have hStar := H.truth_lemma_prop (H.model.F.star w) φ hφ
    constructor
    · intro hNotMem hMemStar
      have hSatNot : RM.sat H.model H.valuation w (.not φ) := hNot.2 hNotMem
      have hNotSatStar : ¬ RM.sat H.model H.valuation (H.model.F.star w) φ := by
        simpa [RM.sat] using hSatNot
      exact hNotSatStar (hStar.2 hMemStar)
    · intro hNotMem
      have hNotSatStar : ¬ RM.sat H.model H.valuation (H.model.F.star w) φ := by
        intro hSatStar
        exact hNotMem (hStar.1 hSatStar)
      have hSatNot : RM.sat H.model H.valuation w (.not φ) := by
        simpa [RM.sat] using hNotSatStar
      exact hNot.1 hSatNot
  imp_mem_iff_prop := by
    intro w φ ψ hφ hψ
    have hImp := H.truth_lemma_prop w (.imp φ ψ) (KripkeProp.IsProp.imp hφ hψ)
    constructor
    · intro hImpMem
      have hSatImp : RM.sat H.model H.valuation w (.imp φ ψ) := hImp.2 hImpMem
      intro u v hR hMemU
      have hSatU : RM.sat H.model H.valuation u φ := (H.truth_lemma_prop u φ hφ).2 hMemU
      have hSatV : RM.sat H.model H.valuation v ψ := hSatImp u v hR hSatU
      exact (H.truth_lemma_prop v ψ hψ).1 hSatV
    · intro hRel
      have hSatImp : RM.sat H.model H.valuation w (.imp φ ψ) := by
        intro u v hR hSatU
        have hMemU : φ ∈ u.carrier := (H.truth_lemma_prop u φ hφ).1 hSatU
        have hMemV : ψ ∈ v.carrier := hRel u v hR hMemU
        exact (H.truth_lemma_prop v ψ hψ).2 hMemV
      exact hImp.1 hSatImp

instance hasPrimeTheoryTruthObligationsProp_of_modelProp
    (σ : Type) [HasPrimeTheoryTruthModelProp σ] :
    HasPrimeTheoryTruthObligationsProp σ :=
  primeTruthObligationsPropOfModelProp (σ := σ)

/--
Canonical propositional RM frame obligations over prime worlds.

This packages the hard canonical clauses directly at the set-membership level and
instantiates `HasPrimeTheoryTruthObligationsProp` via `CanonicalCandidate`.
-/
class HasCanonicalStarProp (σ : Type) where
  starWorld : PrimeTheory σ → PrimeTheory σ
  mem_star_iff_not_mem_not :
    ∀ (w : PrimeTheory σ) (φ : Formula σ),
      KripkeProp.IsProp (σ := σ) φ →
        (φ ∈ (starWorld w).carrier ↔ (.not φ) ∉ w.carrier)

class HasCanonicalStarExistsProp (σ : Type) where
  exists_star :
    ∀ (w : PrimeTheory σ),
      ∃ ws : PrimeTheory σ, ∀ (φ : Formula σ),
        KripkeProp.IsProp (σ := σ) φ →
          (φ ∈ ws.carrier ↔ (.not φ) ∉ w.carrier)

class HasCanonicalImpCompleteProp (σ : Type) where
  imp_complete_prop :
    ∀ (w : PrimeTheory σ) (φ ψ : Formula σ),
      KripkeProp.IsProp (σ := σ) φ →
        KripkeProp.IsProp (σ := σ) ψ →
          (∀ u v, canonicalRworld w u v → (φ ∈ u.carrier → ψ ∈ v.carrier)) →
            (.imp φ ψ) ∈ w.carrier

class HasCanonicalImpCounterexampleProp (σ : Type) where
  counterexample :
    ∀ (w : PrimeTheory σ) (φ ψ : Formula σ),
      KripkeProp.IsProp (σ := σ) φ →
        KripkeProp.IsProp (σ := σ) ψ →
          (.imp φ ψ) ∉ w.carrier →
            ∃ u v : PrimeTheory σ, canonicalRworld w u v ∧ φ ∈ u.carrier ∧ ψ ∉ v.carrier

namespace CanonicalPair

structure State (σ : Type) where
  left  : Set (Formula σ)
  right : Set (Formula σ)

def LE {σ : Type} (s t : State σ) : Prop :=
  s.left ⊆ t.left ∧ s.right ⊆ t.right

instance instPreorderState {σ : Type} : Preorder (State σ) where
  le := LE
  le_refl s := ⟨subset_rfl, subset_rfl⟩
  le_trans a b c hab hbc :=
    ⟨fun χ hχ => hbc.1 (hab.1 hχ), fun χ hχ => hbc.2 (hab.2 hχ)⟩

def sUnion {σ : Type} (c : Set (State σ)) : State σ where
  left := {χ | ∃ s ∈ c, χ ∈ s.left}
  right := {χ | ∃ s ∈ c, χ ∈ s.right}

lemma mem_sUnion_left_iff {σ : Type} {c : Set (State σ)} {χ : Formula σ} :
    χ ∈ (sUnion c).left ↔ ∃ s ∈ c, χ ∈ s.left :=
  Iff.rfl

lemma mem_sUnion_right_iff {σ : Type} {c : Set (State σ)} {χ : Formula σ} :
    χ ∈ (sUnion c).right ↔ ∃ s ∈ c, χ ∈ s.right :=
  Iff.rfl

def defaultState {σ : Type} (w : PrimeTheory σ) (φ : Formula σ) : State σ where
  left := {χ | χ = φ}
  right := {χ | KripkeProp.IsProp (σ := σ) χ ∧ (.imp φ χ) ∈ w.carrier}

def Family {σ : Type} (w : PrimeTheory σ) (φ ψ : Formula σ) : Set (State σ) :=
  {s |
    φ ∈ s.left ∧
    ψ ∉ s.right ∧
    (∀ α β : Formula σ,
      KripkeProp.IsProp (σ := σ) α →
      KripkeProp.IsProp (σ := σ) β →
      (.imp α β) ∈ w.carrier →
      α ∈ s.left →
      β ∈ s.right)}

lemma canonical_constraint_of_mem
    {σ : Type} {w : PrimeTheory σ} {φ ψ : Formula σ}
    {s : State σ}
    (hs : s ∈ Family w φ ψ) :
    ∀ α β : Formula σ,
      KripkeProp.IsProp (σ := σ) α →
      KripkeProp.IsProp (σ := σ) β →
      (.imp α β) ∈ w.carrier →
      α ∈ s.left →
      β ∈ s.right :=
  hs.2.2

lemma imp_not_mem_of_family
    {σ : Type} {w : PrimeTheory σ} {φ ψ : Formula σ}
    {s : State σ}
    (hs : s ∈ Family w φ ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ)
    (hψ : KripkeProp.IsProp (σ := σ) ψ) :
    (.imp φ ψ) ∉ w.carrier := by
  intro hImp
  have hψRight : ψ ∈ s.right := hs.2.2 φ ψ hφ hψ hImp hs.1
  exact hs.2.1 hψRight

lemma defaultState_mem_family
    {σ : Type} {w : PrimeTheory σ} {φ ψ : Formula σ}
    (hφ : KripkeProp.IsProp (σ := σ) φ)
    (hImpNotMem : (.imp φ ψ) ∉ w.carrier) :
    defaultState w φ ∈ Family w φ ψ := by
  constructor
  · simp [defaultState]
  constructor
  · intro hψRight
    exact hImpNotMem (hψRight.2)
  · intro α β hαp hβp hImpMem hα
    have hEq : α = φ := by simpa [defaultState] using hα
    subst hEq
    exact ⟨hβp, hImpMem⟩

lemma sUnion_mem_family
    {σ : Type} {w : PrimeTheory σ} {φ ψ : Formula σ}
    {c : Set (State σ)}
    (hcF : c ⊆ Family w φ ψ)
    (hcne : c.Nonempty) :
    sUnion c ∈ Family w φ ψ := by
  constructor
  · rcases hcne with ⟨s0, hs0⟩
    exact ⟨s0, hs0, (hcF hs0).1⟩
  constructor
  · intro hψ
    rcases hψ with ⟨s, hs, hMem⟩
    exact (hcF hs).2.1 hMem
  · intro α β hαp hβp hImpMem hα
    rcases hα with ⟨s, hs, hMemα⟩
    have hMemβ : β ∈ s.right := (hcF hs).2.2 α β hαp hβp hImpMem hMemα
    exact ⟨s, hs, hMemβ⟩

lemma le_sUnion_of_mem
    {σ : Type} {c : Set (State σ)} {s : State σ}
    (hs : s ∈ c) :
    s ≤ sUnion c := by
  constructor
  · intro χ hχ
    exact ⟨s, hs, hχ⟩
  · intro χ hχ
    exact ⟨s, hs, hχ⟩

theorem exists_maximal
    {σ : Type} (w : PrimeTheory σ) (φ ψ : Formula σ)
    (hφ : KripkeProp.IsProp (σ := σ) φ)
    (hImpNotMem : (.imp φ ψ) ∉ w.carrier) :
    ∃ m : State σ,
      defaultState w φ ≤ m ∧
        Maximal (· ∈ Family w φ ψ) m := by
  have hSeed : defaultState w φ ∈ Family w φ ψ :=
    defaultState_mem_family (w := w) (φ := φ) (ψ := ψ) hφ hImpNotMem
  have hUb :
      ∀ c ⊆ Family w φ ψ, IsChain (· ≤ ·) c →
        ∀ y ∈ c, ∃ ub ∈ Family w φ ψ, ∀ z ∈ c, z ≤ ub := by
    intro c hcF hc y hy
    refine ⟨sUnion c, sUnion_mem_family (w := w) (φ := φ) (ψ := ψ) (hcF := hcF) ⟨y, hy⟩, ?_⟩
    intro z hz
    exact le_sUnion_of_mem hz
  exact zorn_le_nonempty₀ (s := Family w φ ψ) hUb (x := defaultState w φ) hSeed

def rightSeed {σ : Type} (w : PrimeTheory σ) (θ : Formula σ) : Set (Formula σ) :=
  {β | KripkeProp.IsProp (σ := σ) β ∧ (.imp θ β) ∈ w.carrier}

def extendLeft {σ : Type} (w : PrimeTheory σ) (s : State σ) (θ : Formula σ) : State σ where
  left := Set.insert θ s.left
  right := s.right ∪ rightSeed w θ

lemma extendLeft_mem_family_of_not_imp
    {σ : Type} {w : PrimeTheory σ} {φ ψ : Formula σ}
    {s : State σ} {θ : Formula σ}
    (hs : s ∈ Family w φ ψ)
    (hImpNot : (.imp θ ψ) ∉ w.carrier) :
    extendLeft w s θ ∈ Family w φ ψ := by
  constructor
  · exact Or.inr hs.1
  constructor
  · intro hψ
    rcases hψ with hψL | hψR
    · exact hs.2.1 hψL
    · exact hImpNot hψR.2
  · intro α β hαp hβp hImpMem hα
    rcases hα with hαEq | hαOld
    · subst hαEq
      exact Or.inr ⟨hβp, hImpMem⟩
    · exact Or.inl (hs.2.2 α β hαp hβp hImpMem hαOld)

lemma le_extendLeft
    {σ : Type} {w : PrimeTheory σ} {s : State σ} {θ : Formula σ} :
    s ≤ extendLeft w s θ := by
  constructor
  · intro χ hχ
    exact Or.inr hχ
  · intro χ hχ
    exact Or.inl hχ

theorem imp_mem_of_not_mem_left_of_maximal
    {σ : Type} {w : PrimeTheory σ} {φ ψ : Formula σ}
    {m : State σ}
    (hMax : Maximal (· ∈ Family w φ ψ) m)
    {θ : Formula σ}
    (hθNotMem : θ ∉ m.left) :
    (.imp θ ψ) ∈ w.carrier := by
  by_contra hImpNot
  have hExtFam : extendLeft w m θ ∈ Family w φ ψ :=
    extendLeft_mem_family_of_not_imp (hs := hMax.1) (hImpNot := hImpNot)
  have hLeExt : m ≤ extendLeft w m θ := le_extendLeft (w := w) (s := m) (θ := θ)
  have hLeBack : extendLeft w m θ ≤ m := hMax.2 hExtFam hLeExt
  have hθInExt : θ ∈ (extendLeft w m θ).left := Or.inl rfl
  exact hθNotMem (hLeBack.1 hθInExt)

def extendRight {σ : Type} (s : State σ) (χ : Formula σ) : State σ where
  left := s.left
  right := Set.insert χ s.right

lemma extendRight_mem_family_of_ne
    {σ : Type} {w : PrimeTheory σ} {φ ψ : Formula σ}
    {s : State σ} {χ : Formula σ}
    (hs : s ∈ Family w φ ψ)
    (hχ : χ ≠ ψ) :
    extendRight s χ ∈ Family w φ ψ := by
  constructor
  · exact hs.1
  constructor
  · intro hψ
    rcases hψ with hEq | hOld
    · exact hχ (Eq.symm hEq)
    · exact hs.2.1 hOld
  · intro α β hαp hβp hImpMem hα
    exact Or.inr (hs.2.2 α β hαp hβp hImpMem hα)

lemma le_extendRight
    {σ : Type} {s : State σ} {χ : Formula σ} :
    s ≤ extendRight s χ := by
  constructor
  · intro θ hθ
    exact hθ
  · intro θ hθ
    exact Or.inr hθ

theorem mem_right_of_ne_of_maximal
    {σ : Type} {w : PrimeTheory σ} {φ ψ : Formula σ}
    {m : State σ}
    (hMax : Maximal (· ∈ Family w φ ψ) m)
    {χ : Formula σ}
    (hχ : χ ≠ ψ) :
    χ ∈ m.right := by
  have hExtFam : extendRight m χ ∈ Family w φ ψ :=
    extendRight_mem_family_of_ne (hs := hMax.1) (hχ := hχ)
  have hLeExt : m ≤ extendRight m χ := le_extendRight (s := m) (χ := χ)
  have hLeBack : extendRight m χ ≤ m := hMax.2 hExtFam hLeExt
  have hχInExt : χ ∈ (extendRight m χ).right := Or.inl rfl
  exact hLeBack.2 hχInExt

theorem no_prime_extension_of_maximal_right
    {σ : Type} {w : PrimeTheory σ} {φ ψ : Formula σ}
    {m : State σ}
    (hMax : Maximal (· ∈ Family w φ ψ) m)
    (hψ : ψ ≠ (.bot : Formula σ)) :
    ¬ ∃ v : PrimeTheory σ, m.right ⊆ v.carrier := by
  intro hExt
  rcases hExt with ⟨v, hSub⟩
  have hBotMem : (.bot : Formula σ) ∈ m.right :=
    mem_right_of_ne_of_maximal (hMax := hMax) (χ := (.bot : Formula σ))
      (by intro hEq; exact hψ hEq.symm)
  have hBotV : (.bot : Formula σ) ∈ v.carrier := hSub hBotMem
  exact (PrimeTheory.bot_not_mem (w := v)) hBotV

/-
Mixed-order pair states for bi-Lindenbaum recovery:
left grows, right shrinks.
-/
abbrev StateRev (σ : Type) := State σ

instance instPreorderStateRev {σ : Type} : Preorder (StateRev σ) where
  le s t := s.left ⊆ t.left ∧ t.right ⊆ s.right
  lt s t := (s.left ⊆ t.left ∧ t.right ⊆ s.right) ∧ ¬ (t.left ⊆ s.left ∧ s.right ⊆ t.right)
  le_refl s := ⟨subset_rfl, subset_rfl⟩
  le_trans a b c hab hbc :=
    ⟨fun χ hχ => hbc.1 (hab.1 hχ), fun χ hχ => hab.2 (hbc.2 hχ)⟩
  lt_iff_le_not_ge := by
    intro a b
    rfl

def chainUpperRev {σ : Type} (c : Set (StateRev σ)) : StateRev σ where
  left := {χ | ∃ s ∈ c, χ ∈ s.left}
  right := {χ | ∀ s ∈ c, χ ∈ s.right}

lemma chainUpperRev_mem_family
    {σ : Type} {w : PrimeTheory σ} {φ ψ : Formula σ}
    {c : Set (StateRev σ)}
    (hcF : c ⊆ Family w φ ψ)
    (hc : IsChain (· ≤ ·) c)
    (hcne : c.Nonempty) :
    (chainUpperRev c : State σ) ∈ Family w φ ψ := by
  constructor
  · rcases hcne with ⟨s0, hs0⟩
    exact ⟨s0, hs0, (hcF hs0).1⟩
  constructor
  · intro hψ
    rcases hcne with ⟨s0, hs0⟩
    exact (hcF hs0).2.1 (hψ s0 hs0)
  · intro α β hαp hβp hImpMem hα
    rcases hα with ⟨s0, hs0, hα0⟩
    intro t ht
    rcases hc.total hs0 ht with hs0t | hts0
    · have hαt : α ∈ t.left := hs0t.1 hα0
      exact (hcF ht).2.2 α β hαp hβp hImpMem hαt
    · have hβs0 : β ∈ s0.right :=
        (hcF hs0).2.2 α β hαp hβp hImpMem hα0
      exact hts0.2 hβs0

lemma le_chainUpperRev_of_mem
    {σ : Type} {c : Set (StateRev σ)} {s : StateRev σ}
    (hs : s ∈ c) :
    s ≤ chainUpperRev c := by
  constructor
  · intro χ hχ
    exact ⟨s, hs, hχ⟩
  · intro χ hχ
    exact hχ s hs

theorem exists_maximal_mixed
    {σ : Type} (w : PrimeTheory σ) (φ ψ : Formula σ)
    (hφ : KripkeProp.IsProp (σ := σ) φ)
    (hImpNotMem : (.imp φ ψ) ∉ w.carrier) :
    ∃ m : StateRev σ,
      (defaultState w φ : StateRev σ) ≤ m ∧
        Maximal (· ∈ Family w φ ψ) m := by
  have hSeed : (defaultState w φ : StateRev σ) ∈ Family w φ ψ :=
    defaultState_mem_family (w := w) (φ := φ) (ψ := ψ) hφ hImpNotMem
  have hUb :
      ∀ c ⊆ Family w φ ψ, IsChain (· ≤ ·) c →
        ∀ y ∈ c, ∃ ub ∈ Family w φ ψ, ∀ z ∈ c, z ≤ ub := by
    intro c hcF hc y hy
    refine ⟨chainUpperRev c, chainUpperRev_mem_family (w := w) (φ := φ) (ψ := ψ) hcF hc ⟨y, hy⟩, ?_⟩
    intro z hz
    exact le_chainUpperRev_of_mem hz
  exact zorn_le_nonempty₀ (s := Family w φ ψ) hUb (x := (defaultState w φ : StateRev σ)) hSeed

def extendLeftKeepRight {σ : Type} (s : StateRev σ) (θ : Formula σ) : StateRev σ where
  left := Set.insert θ s.left
  right := s.right

lemma le_extendLeftKeepRight
    {σ : Type} {s : StateRev σ} {θ : Formula σ} :
    s ≤ extendLeftKeepRight s θ := by
  constructor
  · intro χ hχ
    exact Or.inr hχ
  · intro χ hχ
    simpa [extendLeftKeepRight] using hχ

theorem exists_right_gap_of_not_mem_left_of_maximal_mixed
    {σ : Type} {w : PrimeTheory σ} {φ ψ : Formula σ}
    {m : StateRev σ}
    (hMax : Maximal (· ∈ Family w φ ψ) m)
    {θ : Formula σ}
    (hθNotMem : θ ∉ m.left) :
    ∃ β : Formula σ,
      KripkeProp.IsProp (σ := σ) β ∧
      (.imp θ β) ∈ w.carrier ∧
      β ∉ m.right := by
  let t : StateRev σ := extendLeftKeepRight m θ
  have hNotFam : t ∉ Family w φ ψ := by
    intro htFam
    have hLe : m ≤ t := le_extendLeftKeepRight (s := m) (θ := θ)
    have hBack : t ≤ m := hMax.2 htFam hLe
    have hθInT : θ ∈ t.left := Or.inl rfl
    exact hθNotMem (hBack.1 hθInT)
  have hmFam : m ∈ Family w φ ψ := hMax.1
  have hφInT : φ ∈ t.left := Or.inr hmFam.1
  have hψNotInT : ψ ∉ t.right := by
    simpa [t, extendLeftKeepRight] using hmFam.2.1
  have hNotConstraint :
      ¬ (∀ α β : Formula σ,
        KripkeProp.IsProp (σ := σ) α →
        KripkeProp.IsProp (σ := σ) β →
        (.imp α β) ∈ w.carrier →
        α ∈ t.left →
        β ∈ t.right) := by
    intro hConstraint
    exact hNotFam ⟨hφInT, hψNotInT, hConstraint⟩
  by_contra hNo
  have hConstraint :
      ∀ α β : Formula σ,
        KripkeProp.IsProp (σ := σ) α →
        KripkeProp.IsProp (σ := σ) β →
        (.imp α β) ∈ w.carrier →
        α ∈ t.left →
        β ∈ t.right := by
    intro α β hαp hβp hImp hαIn
    rcases hαIn with hαEq | hαMem
    · subst hαEq
      have hβInM : β ∈ m.right := by
        by_contra hβNot
        exact hNo ⟨β, hβp, hImp, hβNot⟩
      simpa [t, extendLeftKeepRight] using hβInM
    · have hβInM : β ∈ m.right := hmFam.2.2 α β hαp hβp hImp hαMem
      simpa [t, extendLeftKeepRight] using hβInM
  exact hNotConstraint hConstraint

def shrinkRight {σ : Type} (s : StateRev σ) (χ : Formula σ) : StateRev σ where
  left := s.left
  right := s.right \ ({χ} : Set (Formula σ))

lemma le_shrinkRight_of_mem
    {σ : Type} {s : StateRev σ} {χ : Formula σ} :
    s ≤ shrinkRight s χ := by
  constructor
  · intro θ hθ
    simpa [shrinkRight] using hθ
  · intro θ hθ
    exact hθ.1

theorem exists_left_support_of_mem_right_of_maximal_mixed
    {σ : Type} {w : PrimeTheory σ} {φ ψ : Formula σ}
    {m : StateRev σ}
    (hMax : Maximal (· ∈ Family w φ ψ) m)
    {χ : Formula σ}
    (hχMem : χ ∈ m.right) :
    ∃ α : Formula σ,
      α ∈ m.left ∧
      KripkeProp.IsProp (σ := σ) α ∧
      (.imp α χ) ∈ w.carrier := by
  let t : StateRev σ := shrinkRight m χ
  have hNotFam : t ∉ Family w φ ψ := by
    intro htFam
    have hLe : m ≤ t := le_shrinkRight_of_mem (s := m) (χ := χ)
    have hBack : t ≤ m := hMax.2 htFam hLe
    have hχInT : χ ∈ t.right := hBack.2 hχMem
    have hχNotInT : χ ∉ t.right := by
      simp [t, shrinkRight]
    exact hχNotInT hχInT
  have hmFam : m ∈ Family w φ ψ := hMax.1
  have hφInT : φ ∈ t.left := by
    simpa [t, shrinkRight] using hmFam.1
  have hψNotInT : ψ ∉ t.right := by
    intro hψInT
    exact hmFam.2.1 hψInT.1
  have hNotConstraint :
      ¬ (∀ α β : Formula σ,
        KripkeProp.IsProp (σ := σ) α →
        KripkeProp.IsProp (σ := σ) β →
        (.imp α β) ∈ w.carrier →
        α ∈ t.left →
        β ∈ t.right) := by
    intro hConstraint
    exact hNotFam ⟨hφInT, hψNotInT, hConstraint⟩
  have hConstraintFail :
      ∃ α β : Formula σ,
        KripkeProp.IsProp (σ := σ) α ∧
        KripkeProp.IsProp (σ := σ) β ∧
        (.imp α β) ∈ w.carrier ∧
        α ∈ t.left ∧
        β ∉ t.right := by
    by_contra hAll
    apply hNotConstraint
    intro α β hαp hβp hImp hαIn
    by_contra hβNot
    exact hAll ⟨α, β, hαp, hβp, hImp, hαIn, hβNot⟩
  rcases hConstraintFail with ⟨α, β, hαp, hβp, hImp, hαInT, hβNotInT⟩
  have hαInM : α ∈ m.left := by
    simpa [t, shrinkRight] using hαInT
  have hβInM : β ∈ m.right := hmFam.2.2 α β hαp hβp hImp hαInM
  have hNotInDiff : β ∉ m.right \ ({χ} : Set (Formula σ)) := by
    simpa [t, shrinkRight] using hβNotInT
  have hβEq : β = χ := by
    by_contra hβNe
    have hβNotSingleton : β ∉ ({χ} : Set (Formula σ)) := by
      simp [Set.mem_singleton_iff, hβNe]
    exact hNotInDiff ⟨hβInM, hβNotSingleton⟩
  subst hβEq
  exact ⟨α, hαInM, hαp, hImp⟩

theorem mem_left_iff_blocks_right_of_maximal_mixed
    {σ : Type} {w : PrimeTheory σ} {φ ψ : Formula σ}
    {m : StateRev σ}
    (hMax : Maximal (· ∈ Family w φ ψ) m)
    {θ : Formula σ}
    (hθProp : KripkeProp.IsProp (σ := σ) θ) :
    θ ∈ m.left ↔
      ∀ β : Formula σ,
        KripkeProp.IsProp (σ := σ) β →
          (.imp θ β) ∈ w.carrier →
            β ∈ m.right := by
  constructor
  · intro hθ β hβp hImp
    exact hMax.1.2.2 θ β hθProp hβp hImp hθ
  · intro hBlock
    by_contra hθNotMem
    rcases exists_right_gap_of_not_mem_left_of_maximal_mixed
      (hMax := hMax) (θ := θ) hθNotMem with
      ⟨β, hβp, hImp, hβNotMem⟩
    exact hβNotMem (hBlock β hβp hImp)

theorem mem_right_iff_left_support_of_maximal_mixed
    {σ : Type} {w : PrimeTheory σ} {φ ψ : Formula σ}
    {m : StateRev σ}
    (hMax : Maximal (· ∈ Family w φ ψ) m)
    {χ : Formula σ}
    (hχProp : KripkeProp.IsProp (σ := σ) χ) :
    χ ∈ m.right ↔
      ∃ α : Formula σ,
        α ∈ m.left ∧
        KripkeProp.IsProp (σ := σ) α ∧
        (.imp α χ) ∈ w.carrier := by
  constructor
  · intro hχMem
    exact exists_left_support_of_mem_right_of_maximal_mixed
      (hMax := hMax) (χ := χ) hχMem
  · intro hSupport
    rcases hSupport with ⟨α, hαMem, hαProp, hImp⟩
    exact hMax.1.2.2 α χ hαProp hχProp hImp hαMem

/--
Realization interface for the mixed maximal-state bottleneck.

Given a maximal mixed state `m` in `Family w φ ψ`, provide prime theories `u, v`
that propositionally reflect `m.left` and `m.right`.
-/
class HasMaximalMixedPrimeRealization (σ : Type) : Prop where
  realize :
    ∀ (w : PrimeTheory σ) (φ ψ : Formula σ) (m : StateRev σ),
      KripkeProp.IsProp (σ := σ) φ →
      KripkeProp.IsProp (σ := σ) ψ →
      Maximal (· ∈ Family w φ ψ) m →
      ∃ u v : PrimeTheory σ,
        (∀ α : Formula σ,
          KripkeProp.IsProp (σ := σ) α →
            (α ∈ u.carrier ↔ α ∈ m.left)) ∧
        (∀ β : Formula σ,
          KripkeProp.IsProp (σ := σ) β →
            (β ∈ v.carrier ↔ β ∈ m.right))

/--
Split realization obligations for maximal mixed states.

This decomposes `HasMaximalMixedPrimeRealization` into independent left/right targets,
which is often easier to realize constructively.
-/
class HasMaximalMixedLeftPrimeRealization (σ : Type) : Prop where
  realize_left :
    ∀ (w : PrimeTheory σ) (φ ψ : Formula σ) (m : StateRev σ),
      KripkeProp.IsProp (σ := σ) φ →
      KripkeProp.IsProp (σ := σ) ψ →
      Maximal (· ∈ Family w φ ψ) m →
      ∃ u : PrimeTheory σ,
        ∀ α : Formula σ,
          KripkeProp.IsProp (σ := σ) α →
            (α ∈ u.carrier ↔ α ∈ m.left)

class HasMaximalMixedRightPrimeRealization (σ : Type) : Prop where
  realize_right :
    ∀ (w : PrimeTheory σ) (φ ψ : Formula σ) (m : StateRev σ),
      KripkeProp.IsProp (σ := σ) φ →
      KripkeProp.IsProp (σ := σ) ψ →
      Maximal (· ∈ Family w φ ψ) m →
      ∃ v : PrimeTheory σ,
        ∀ β : Formula σ,
          KripkeProp.IsProp (σ := σ) β →
            (β ∈ v.carrier ↔ β ∈ m.right)

theorem hasMaximalMixedPrimeRealization_of_split
    {σ : Type}
    [HasMaximalMixedLeftPrimeRealization σ]
    [HasMaximalMixedRightPrimeRealization σ] :
    HasMaximalMixedPrimeRealization σ := by
  refine ⟨?_⟩
  intro w φ ψ m hφ hψ hMax
  rcases HasMaximalMixedLeftPrimeRealization.realize_left (σ := σ) w φ ψ m hφ hψ hMax with
    ⟨u, hLeft⟩
  rcases HasMaximalMixedRightPrimeRealization.realize_right (σ := σ) w φ ψ m hφ hψ hMax with
    ⟨v, hRight⟩
  exact ⟨u, v, hLeft, hRight⟩

instance hasMaximalMixedLeftPrimeRealization_of_full
    (σ : Type) [HasMaximalMixedPrimeRealization σ] :
    HasMaximalMixedLeftPrimeRealization σ where
  realize_left := by
    intro w φ ψ m hφ hψ hMax
    rcases HasMaximalMixedPrimeRealization.realize (σ := σ) w φ ψ m hφ hψ hMax with
      ⟨u, _v, hLeft, _hRight⟩
    exact ⟨u, hLeft⟩

instance hasMaximalMixedRightPrimeRealization_of_full
    (σ : Type) [HasMaximalMixedPrimeRealization σ] :
    HasMaximalMixedRightPrimeRealization σ where
  realize_right := by
    intro w φ ψ m hφ hψ hMax
    rcases HasMaximalMixedPrimeRealization.realize (σ := σ) w φ ψ m hφ hψ hMax with
      ⟨_u, v, _hLeft, hRight⟩
    exact ⟨v, hRight⟩

/--
Directional maximal-mixed realization payload.

Compared with full left/right bi-equivalence, this only asks for transfer directions
needed to build `HasPrimeTransferLift`.
-/
class HasMaximalMixedTransferRealization (σ : Type) : Prop where
  transfer :
    ∀ (w : PrimeTheory σ) (φ ψ : Formula σ) (m : StateRev σ),
      KripkeProp.IsProp (σ := σ) φ →
      KripkeProp.IsProp (σ := σ) ψ →
      Maximal (· ∈ Family w φ ψ) m →
      ∃ u v : PrimeTheory σ,
        φ ∈ u.carrier ∧
        ψ ∉ v.carrier ∧
        (∀ α : Formula σ,
          KripkeProp.IsProp (σ := σ) α →
            α ∈ u.carrier →
              α ∈ m.left) ∧
        (∀ β : Formula σ,
          KripkeProp.IsProp (σ := σ) β →
            β ∈ m.right →
              β ∈ v.carrier)

class HasMaximalMixedLeftInRealization (σ : Type) : Prop where
  realize_leftIn :
    ∀ (w : PrimeTheory σ) (φ ψ : Formula σ) (m : StateRev σ),
      KripkeProp.IsProp (σ := σ) φ →
      KripkeProp.IsProp (σ := σ) ψ →
      Maximal (· ∈ Family w φ ψ) m →
      ∃ u : PrimeTheory σ,
        φ ∈ u.carrier ∧
        ∀ α : Formula σ,
          KripkeProp.IsProp (σ := σ) α →
            α ∈ u.carrier →
              α ∈ m.left

class HasMaximalMixedRightOutRealization (σ : Type) : Prop where
  realize_rightOut :
    ∀ (w : PrimeTheory σ) (φ ψ : Formula σ) (m : StateRev σ),
      KripkeProp.IsProp (σ := σ) φ →
      KripkeProp.IsProp (σ := σ) ψ →
      Maximal (· ∈ Family w φ ψ) m →
      ∃ v : PrimeTheory σ,
        ψ ∉ v.carrier ∧
        ∀ β : Formula σ,
          KripkeProp.IsProp (σ := σ) β →
            β ∈ m.right →
              β ∈ v.carrier

/--
Propositional slice of a maximal mixed state's right component.
-/
def rightPropSet {σ : Type} (m : StateRev σ) : Set (Formula σ) :=
  {β | KripkeProp.IsProp (σ := σ) β ∧ β ∈ m.right}

/--
Propositional formulas missing from a maximal mixed state's left component.
-/
def leftPropGapSet {σ : Type} (m : StateRev σ) : Set (Formula σ) :=
  {α | KripkeProp.IsProp (σ := σ) α ∧ α ∉ m.left}

/--
Propositional slice of a maximal mixed state's left component.
-/
def leftPropSet {σ : Type} (m : StateRev σ) : Set (Formula σ) :=
  {α | KripkeProp.IsProp (σ := σ) α ∧ α ∈ m.left}

/--
Set-avoid prime extension interface.

Given a base set `S` and a set of formulas `C` that are all non-derivable from `S`,
produce a prime theory extending `S` while avoiding membership of every formula in `C`.
-/
class HasPrimeTheoryAvoidSet (σ : Type) : Prop where
  exists_primeTheory_avoid_set :
    ∀ (S C : Set (Formula σ)),
      (∀ χ ∈ C, ¬ Derivable S χ) →
      ∃ W : PrimeTheory σ, S ⊆ W.carrier ∧ ∀ χ ∈ C, χ ∉ W.carrier

/--
Left-side derivability gap needed to construct `HasMaximalMixedLeftInRealization`
via set-avoid prime extension.
-/
class HasMaximalMixedLeftDerivabilityGap (σ : Type) : Prop where
  avoid_left :
    ∀ (w : PrimeTheory σ) (φ ψ : Formula σ) (m : StateRev σ),
      KripkeProp.IsProp (σ := σ) φ →
      KripkeProp.IsProp (σ := σ) ψ →
      Maximal (· ∈ Family w φ ψ) m →
      ∀ χ, χ ∈ leftPropGapSet m → ¬ Derivable (leftPropSet m) χ

/--
Right-side derivability gap needed to construct `HasMaximalMixedRightOutRealization`
via Lindenbaum avoidance.
-/
class HasMaximalMixedRightDerivabilityGap (σ : Type) : Prop where
  avoid_right :
    ∀ (w : PrimeTheory σ) (φ ψ : Formula σ) (m : StateRev σ),
      KripkeProp.IsProp (σ := σ) φ →
      KripkeProp.IsProp (σ := σ) ψ →
      Maximal (· ∈ Family w φ ψ) m →
      ¬ Derivable (rightPropSet m) ψ

theorem hasMaximalMixedRightOutRealization_of_rightDerivabilityGap
    {σ : Type}
    [HasMaximalMixedRightDerivabilityGap σ] :
    HasMaximalMixedRightOutRealization σ := by
  refine ⟨?_⟩
  intro w φ ψ m hφ hψ hMax
  have hAvoid : ¬ Derivable (rightPropSet m) ψ :=
    HasMaximalMixedRightDerivabilityGap.avoid_right (σ := σ) w φ ψ m hφ hψ hMax
  rcases LindenbaumAvoid.exists_primeTheory_avoid (S := rightPropSet m) (χ := ψ) hAvoid with
    ⟨v, hS, hNotψv⟩
  refine ⟨v, hNotψv, ?_⟩
  intro β hβp hβm
  exact hS ⟨hβp, hβm⟩

instance (priority := low) hasMaximalMixedRightOutRealization_of_rightDerivabilityGap_inst
    (σ : Type)
    [HasMaximalMixedRightDerivabilityGap σ] :
    HasMaximalMixedRightOutRealization σ :=
  hasMaximalMixedRightOutRealization_of_rightDerivabilityGap (σ := σ)

theorem hasMaximalMixedLeftInRealization_of_avoidSet_and_leftDerivabilityGap
    {σ : Type}
    [HasPrimeTheoryAvoidSet σ]
    [HasMaximalMixedLeftDerivabilityGap σ] :
    HasMaximalMixedLeftInRealization σ := by
  refine ⟨?_⟩
  intro w φ ψ m hφ hψ hMax
  have hm : m ∈ Family w φ ψ := hMax.1
  let S : Set (Formula σ) := leftPropSet m
  let C : Set (Formula σ) := leftPropGapSet m
  have hC : ∀ χ ∈ C, ¬ Derivable S χ := by
    intro χ hχ
    exact HasMaximalMixedLeftDerivabilityGap.avoid_left
      (σ := σ) w φ ψ m hφ hψ hMax χ (by simpa [C] using hχ)
  rcases HasPrimeTheoryAvoidSet.exists_primeTheory_avoid_set
      (σ := σ) S C hC with ⟨u, hS, hAvoid⟩
  have hφS : φ ∈ S := ⟨hφ, hm.1⟩
  refine ⟨u, hS hφS, ?_⟩
  intro α hαp hαu
  by_contra hαNotLeft
  have hαGap : α ∈ C := by
    exact ⟨hαp, hαNotLeft⟩
  exact (hAvoid α hαGap) hαu

instance (priority := low) hasMaximalMixedLeftInRealization_of_avoidSet_and_leftDerivabilityGap_inst
    (σ : Type)
    [HasPrimeTheoryAvoidSet σ]
    [HasMaximalMixedLeftDerivabilityGap σ] :
    HasMaximalMixedLeftInRealization σ :=
  hasMaximalMixedLeftInRealization_of_avoidSet_and_leftDerivabilityGap (σ := σ)

instance hasMaximalMixedLeftInRealization_of_left
    (σ : Type) [HasMaximalMixedLeftPrimeRealization σ] :
    HasMaximalMixedLeftInRealization σ where
  realize_leftIn := by
    intro w φ ψ m hφ hψ hMax
    have hm : m ∈ Family w φ ψ := hMax.1
    rcases HasMaximalMixedLeftPrimeRealization.realize_left (σ := σ) w φ ψ m hφ hψ hMax with
      ⟨u, hLeft⟩
    refine ⟨u, ?_, ?_⟩
    · exact (hLeft φ hφ).2 hm.1
    · intro α hαp hαu
      exact (hLeft α hαp).1 hαu

instance hasMaximalMixedRightOutRealization_of_right
    (σ : Type) [HasMaximalMixedRightPrimeRealization σ] :
    HasMaximalMixedRightOutRealization σ where
  realize_rightOut := by
    intro w φ ψ m hφ hψ hMax
    have hm : m ∈ Family w φ ψ := hMax.1
    rcases HasMaximalMixedRightPrimeRealization.realize_right (σ := σ) w φ ψ m hφ hψ hMax with
      ⟨v, hRight⟩
    refine ⟨v, ?_, ?_⟩
    · intro hψv
      exact hm.2.1 ((hRight ψ hψ).1 hψv)
    · intro β hβp hβm
      exact (hRight β hβp).2 hβm

theorem hasMaximalMixedLeftDerivabilityGap_of_leftPrimeRealization
    {σ : Type}
    [HasMaximalMixedLeftPrimeRealization σ] :
    HasMaximalMixedLeftDerivabilityGap σ := by
  refine ⟨?_⟩
  intro w φ ψ m hφ hψ hMax χ hχGap
  rcases hχGap with ⟨hχProp, hχNotLeft⟩
  rcases HasMaximalMixedLeftPrimeRealization.realize_left (σ := σ) w φ ψ m hφ hψ hMax with
    ⟨u, hLeft⟩
  intro hDer
  have hSub : leftPropSet m ⊆ u.carrier := by
    intro θ hθ
    rcases hθ with ⟨hθProp, hθLeft⟩
    exact (hLeft θ hθProp).2 hθLeft
  have hDerU : Derivable u.carrier χ :=
    (Derivable.mono (T := leftPropSet m) (U := u.carrier) hSub) hDer
  have hχu : χ ∈ u.carrier := u.closed χ hDerU
  exact hχNotLeft ((hLeft χ hχProp).1 hχu)

instance (priority := low) hasMaximalMixedLeftDerivabilityGap_of_leftPrimeRealization_inst
    (σ : Type)
    [HasMaximalMixedLeftPrimeRealization σ] :
    HasMaximalMixedLeftDerivabilityGap σ :=
  hasMaximalMixedLeftDerivabilityGap_of_leftPrimeRealization (σ := σ)

theorem hasMaximalMixedRightDerivabilityGap_of_rightPrimeRealization
    {σ : Type}
    [HasMaximalMixedRightPrimeRealization σ] :
    HasMaximalMixedRightDerivabilityGap σ := by
  refine ⟨?_⟩
  intro w φ ψ m hφ hψ hMax
  have hm : m ∈ Family w φ ψ := hMax.1
  rcases HasMaximalMixedRightPrimeRealization.realize_right (σ := σ) w φ ψ m hφ hψ hMax with
    ⟨v, hRight⟩
  intro hDer
  have hSub : rightPropSet m ⊆ v.carrier := by
    intro β hβ
    rcases hβ with ⟨hβProp, hβRight⟩
    exact (hRight β hβProp).2 hβRight
  have hDerV : Derivable v.carrier ψ :=
    (Derivable.mono (T := rightPropSet m) (U := v.carrier) hSub) hDer
  have hψv : ψ ∈ v.carrier := v.closed ψ hDerV
  exact hm.2.1 ((hRight ψ hψ).1 hψv)

instance (priority := low) hasMaximalMixedRightDerivabilityGap_of_rightPrimeRealization_inst
    (σ : Type)
    [HasMaximalMixedRightPrimeRealization σ] :
    HasMaximalMixedRightDerivabilityGap σ :=
  hasMaximalMixedRightDerivabilityGap_of_rightPrimeRealization (σ := σ)

theorem hasMaximalMixedTransferRealization_of_leftIn_rightOut
    {σ : Type}
    [HasMaximalMixedLeftInRealization σ]
    [HasMaximalMixedRightOutRealization σ] :
    HasMaximalMixedTransferRealization σ := by
  refine ⟨?_⟩
  intro w φ ψ m hφ hψ hMax
  rcases HasMaximalMixedLeftInRealization.realize_leftIn (σ := σ) w φ ψ m hφ hψ hMax with
    ⟨u, hφu, hLeftIn⟩
  rcases HasMaximalMixedRightOutRealization.realize_rightOut (σ := σ) w φ ψ m hφ hψ hMax with
    ⟨v, hNotψv, hRightOut⟩
  exact ⟨u, v, hφu, hNotψv, hLeftIn, hRightOut⟩

instance (priority := low) hasMaximalMixedTransferRealization_of_leftIn_rightOut_inst
    (σ : Type)
    [HasMaximalMixedLeftInRealization σ]
    [HasMaximalMixedRightOutRealization σ] :
    HasMaximalMixedTransferRealization σ :=
  hasMaximalMixedTransferRealization_of_leftIn_rightOut (σ := σ)

theorem hasMaximalMixedTransferRealization_of_split
    {σ : Type}
    [HasMaximalMixedLeftPrimeRealization σ]
    [HasMaximalMixedRightPrimeRealization σ] :
    HasMaximalMixedTransferRealization σ := by
  letI : HasMaximalMixedLeftInRealization σ :=
    hasMaximalMixedLeftInRealization_of_left (σ := σ)
  letI : HasMaximalMixedRightOutRealization σ :=
    hasMaximalMixedRightOutRealization_of_right (σ := σ)
  exact hasMaximalMixedTransferRealization_of_leftIn_rightOut (σ := σ)

instance (priority := low) hasMaximalMixedTransferRealization_of_split_inst
    (σ : Type)
    [HasMaximalMixedLeftPrimeRealization σ]
    [HasMaximalMixedRightPrimeRealization σ] :
    HasMaximalMixedTransferRealization σ :=
  hasMaximalMixedTransferRealization_of_split (σ := σ)

instance hasMaximalMixedTransferRealization_of_full
    (σ : Type) [HasMaximalMixedPrimeRealization σ] :
    HasMaximalMixedTransferRealization σ where
  transfer := by
    intro w φ ψ m hφ hψ hMax
    have hm : m ∈ Family w φ ψ := hMax.1
    rcases HasMaximalMixedPrimeRealization.realize (σ := σ) w φ ψ m hφ hψ hMax with
      ⟨u, v, hLeft, hRight⟩
    refine ⟨u, v, ?_, ?_, ?_, ?_⟩
    · exact (hLeft φ hφ).2 hm.1
    · intro hψv
      exact hm.2.1 ((hRight ψ hψ).1 hψv)
    · intro α hαp hαu
      exact (hLeft α hαp).1 hαu
    · intro β hβp hβm
      exact (hRight β hβp).2 hβm

class HasPrimeLift (σ : Type) : Prop where
  lift :
    ∀ (w : PrimeTheory σ) (φ ψ : Formula σ),
      KripkeProp.IsProp (σ := σ) φ →
      KripkeProp.IsProp (σ := σ) ψ →
      (.imp φ ψ) ∉ w.carrier →
      ∃ u v : PrimeTheory σ,
        (defaultState w φ).left ⊆ u.carrier ∧
        (defaultState w φ).right ⊆ v.carrier ∧
        ψ ∉ v.carrier ∧
        canonicalRworld w u v

theorem canonicalRworld_of_prop_reflection
    {σ : Type}
    {w : PrimeTheory σ} {φ ψ : Formula σ}
    {m : StateRev σ}
    {u v : PrimeTheory σ}
    (hm : m ∈ Family w φ ψ)
    (hLeftProp :
      ∀ α : Formula σ,
        KripkeProp.IsProp (σ := σ) α →
          (α ∈ u.carrier ↔ α ∈ m.left))
    (hRightProp :
      ∀ β : Formula σ,
        KripkeProp.IsProp (σ := σ) β →
          (β ∈ v.carrier ↔ β ∈ m.right)) :
    canonicalRworld w u v := by
  intro α β hαp hβp hImp hαu
  have hαm : α ∈ m.left := (hLeftProp α hαp).1 hαu
  have hβm : β ∈ m.right := hm.2.2 α β hαp hβp hImp hαm
  exact (hRightProp β hβp).2 hβm

theorem canonicalRworld_of_prop_transfer
    {σ : Type}
    {w : PrimeTheory σ} {φ ψ : Formula σ}
    {m : StateRev σ}
    {u v : PrimeTheory σ}
    (hm : m ∈ Family w φ ψ)
    (hLeftIn :
      ∀ α : Formula σ,
        KripkeProp.IsProp (σ := σ) α →
          α ∈ u.carrier →
          α ∈ m.left)
    (hRightOut :
      ∀ β : Formula σ,
        KripkeProp.IsProp (σ := σ) β →
          β ∈ m.right →
          β ∈ v.carrier) :
    canonicalRworld w u v := by
  intro α β hαp hβp hImp hαu
  have hαm : α ∈ m.left := hLeftIn α hαp hαu
  have hβm : β ∈ m.right := hm.2.2 α β hαp hβp hImp hαm
  exact hRightOut β hβp hβm

/--
Sufficient reflection-style lift interface for canonical pair states.

If each non-implication witness state can be reflected propositionally into a pair of
prime theories (`u`, `v`) preserving left/right propositional membership, then the
required `HasPrimeLift` witness follows.
-/
class HasPrimeReflectionLift (σ : Type) : Prop where
  reflect :
    ∀ (w : PrimeTheory σ) (φ ψ : Formula σ),
      KripkeProp.IsProp (σ := σ) φ →
      KripkeProp.IsProp (σ := σ) ψ →
      (.imp φ ψ) ∉ w.carrier →
      ∃ m : StateRev σ, ∃ u v : PrimeTheory σ,
        m ∈ Family w φ ψ ∧
        (∀ α : Formula σ,
          KripkeProp.IsProp (σ := σ) α →
            (α ∈ u.carrier ↔ α ∈ m.left)) ∧
        (∀ β : Formula σ,
          KripkeProp.IsProp (σ := σ) β →
            (β ∈ v.carrier ↔ β ∈ m.right))

theorem hasPrimeReflectionLift_of_maximalMixedPrimeRealization
    {σ : Type}
    [HasMaximalMixedPrimeRealization σ] :
    HasPrimeReflectionLift σ := by
  refine ⟨?_⟩
  intro w φ ψ hφ hψ hImpNotMem
  rcases exists_maximal_mixed (w := w) (φ := φ) (ψ := ψ) hφ hImpNotMem with
    ⟨m, _hSeedLe, hMax⟩
  have hmFam : m ∈ Family w φ ψ := hMax.1
  rcases HasMaximalMixedPrimeRealization.realize (σ := σ) w φ ψ m hφ hψ hMax with
    ⟨u, v, hLeftProp, hRightProp⟩
  exact ⟨m, u, v, hmFam, hLeftProp, hRightProp⟩

instance hasPrimeReflectionLift_of_maximalMixedPrimeRealization_inst
    (σ : Type)
    [HasMaximalMixedPrimeRealization σ] :
    HasPrimeReflectionLift σ :=
  hasPrimeReflectionLift_of_maximalMixedPrimeRealization (σ := σ)

/--
Directional transfer variant of prime lift.

Compared to `HasPrimeReflectionLift`, this only requires:
- propositional formulas supported by `u` flow into `m.left`,
- propositional formulas in `m.right` flow into `v`.

This is sufficient for proving `canonicalRworld` and hence `HasPrimeLift`.
-/
class HasPrimeTransferLift (σ : Type) : Prop where
  transfer :
    ∀ (w : PrimeTheory σ) (φ ψ : Formula σ),
      KripkeProp.IsProp (σ := σ) φ →
      KripkeProp.IsProp (σ := σ) ψ →
      (.imp φ ψ) ∉ w.carrier →
      ∃ m : StateRev σ, ∃ u v : PrimeTheory σ,
        m ∈ Family w φ ψ ∧
        φ ∈ u.carrier ∧
        ψ ∉ v.carrier ∧
        (∀ α : Formula σ,
          KripkeProp.IsProp (σ := σ) α →
            α ∈ u.carrier →
            α ∈ m.left) ∧
        (∀ β : Formula σ,
          KripkeProp.IsProp (σ := σ) β →
            β ∈ m.right →
            β ∈ v.carrier)

theorem hasPrimeTransferLift_of_maximalMixedTransferRealization
    {σ : Type}
    [HasMaximalMixedTransferRealization σ] :
    HasPrimeTransferLift σ := by
  refine ⟨?_⟩
  intro w φ ψ hφ hψ hImpNotMem
  rcases exists_maximal_mixed (w := w) (φ := φ) (ψ := ψ) hφ hImpNotMem with
    ⟨m, _hSeedLe, hMax⟩
  have hm : m ∈ Family w φ ψ := hMax.1
  rcases HasMaximalMixedTransferRealization.transfer (σ := σ) w φ ψ m hφ hψ hMax with
    ⟨u, v, hφu, hNotψv, hLeftIn, hRightOut⟩
  exact ⟨m, u, v, hm, hφu, hNotψv, hLeftIn, hRightOut⟩

instance hasPrimeTransferLift_of_maximalMixedTransferRealization_inst
    (σ : Type)
    [HasMaximalMixedTransferRealization σ] :
    HasPrimeTransferLift σ :=
  hasPrimeTransferLift_of_maximalMixedTransferRealization (σ := σ)

theorem hasPrimeTransferLift_of_maximalMixed_leftIn_rightOut
    {σ : Type}
    [HasMaximalMixedLeftInRealization σ]
    [HasMaximalMixedRightOutRealization σ] :
    HasPrimeTransferLift σ := by
  letI : HasMaximalMixedTransferRealization σ :=
    hasMaximalMixedTransferRealization_of_leftIn_rightOut (σ := σ)
  exact hasPrimeTransferLift_of_maximalMixedTransferRealization (σ := σ)

instance (priority := low) hasPrimeTransferLift_of_maximalMixed_leftIn_rightOut_inst
    (σ : Type)
    [HasMaximalMixedLeftInRealization σ]
    [HasMaximalMixedRightOutRealization σ] :
    HasPrimeTransferLift σ :=
  hasPrimeTransferLift_of_maximalMixed_leftIn_rightOut (σ := σ)

theorem hasPrimeLift_of_transfer
    {σ : Type}
    [HasPrimeTransferLift σ] :
    HasPrimeLift σ := by
  refine ⟨?_⟩
  intro w φ ψ hφ hψ hImpNotMem
  rcases HasPrimeTransferLift.transfer (σ := σ) w φ ψ hφ hψ hImpNotMem with
    ⟨m, u, v, hm, hφu, hNotψv, hLeftIn, hRightOut⟩
  refine ⟨u, v, ?_, ?_, ?_, ?_⟩
  · intro χ hχ
    have hEq : χ = φ := by simpa [defaultState] using hχ
    simpa [hEq] using hφu
  · intro χ hχ
    rcases hχ with ⟨hχProp, hImpχ⟩
    have hχm : χ ∈ m.right := hm.2.2 φ χ hφ hχProp hImpχ hm.1
    exact hRightOut χ hχProp hχm
  · exact hNotψv
  · exact canonicalRworld_of_prop_transfer hm hLeftIn hRightOut

instance hasPrimeLift_of_transfer_inst
    (σ : Type)
    [HasPrimeTransferLift σ] :
    HasPrimeLift σ :=
  hasPrimeLift_of_transfer (σ := σ)

theorem hasPrimeTransferLift_of_reflection
    {σ : Type}
    [HasPrimeReflectionLift σ] :
    HasPrimeTransferLift σ := by
  refine ⟨?_⟩
  intro w φ ψ hφ hψ hImpNotMem
  rcases HasPrimeReflectionLift.reflect (σ := σ) w φ ψ hφ hψ hImpNotMem with
    ⟨m, u, v, hm, hLeftProp, hRightProp⟩
  have hφu : φ ∈ u.carrier := (hLeftProp φ hφ).2 hm.1
  have hNotψv : ψ ∉ v.carrier := by
    intro hψv
    exact hm.2.1 ((hRightProp ψ hψ).1 hψv)
  refine ⟨m, u, v, hm, hφu, hNotψv, ?_, ?_⟩
  · intro α hαp hαu
    exact (hLeftProp α hαp).1 hαu
  · intro β hβp hβm
    exact (hRightProp β hβp).2 hβm

instance (priority := low) hasPrimeTransferLift_of_reflection_inst
    (σ : Type)
    [HasPrimeReflectionLift σ] :
    HasPrimeTransferLift σ :=
  hasPrimeTransferLift_of_reflection (σ := σ)

instance hasPrimeTransferLift_of_maximalMixedPrimeRealization_inst
    (σ : Type)
    [HasMaximalMixedPrimeRealization σ] :
    HasPrimeTransferLift σ := by
  letI : HasPrimeReflectionLift σ :=
    hasPrimeReflectionLift_of_maximalMixedPrimeRealization (σ := σ)
  exact hasPrimeTransferLift_of_reflection (σ := σ)

theorem hasPrimeLift_of_reflection
    {σ : Type}
    [HasPrimeReflectionLift σ] :
    HasPrimeLift σ := by
  refine ⟨?_⟩
  intro w φ ψ hφ hψ hImpNotMem
  rcases HasPrimeReflectionLift.reflect (σ := σ) w φ ψ hφ hψ hImpNotMem with
    ⟨m, u, v, hm, hLeftProp, hRightProp⟩
  refine ⟨u, v, ?_, ?_, ?_, ?_⟩
  · intro χ hχ
    have hEq : χ = φ := by simpa [defaultState] using hχ
    have hφu : φ ∈ u.carrier := (hLeftProp φ hφ).2 hm.1
    simpa [hEq] using hφu
  · intro χ hχ
    rcases hχ with ⟨hχProp, hImpχ⟩
    have hχm : χ ∈ m.right := hm.2.2 φ χ hφ hχProp hImpχ hm.1
    exact (hRightProp χ hχProp).2 hχm
  · have hψNotM : ψ ∉ m.right := hm.2.1
    intro hψv
    exact hψNotM ((hRightProp ψ hψ).1 hψv)
  · exact canonicalRworld_of_prop_reflection hm hLeftProp hRightProp

instance (priority := low) hasPrimeLift_of_reflection_inst
    (σ : Type)
    [HasPrimeReflectionLift σ] :
    HasPrimeLift σ :=
  hasPrimeLift_of_reflection (σ := σ)

theorem hasPrimeReflectionLift_of_primeLift
    {σ : Type}
    [HasPrimeLift σ] :
    HasPrimeReflectionLift σ := by
  refine ⟨?_⟩
  intro w φ ψ hφ hψ hImpNotMem
  rcases HasPrimeLift.lift (σ := σ) w φ ψ hφ hψ hImpNotMem with
    ⟨u, v, hLeft, hRight, hNotV, hR⟩
  let m : StateRev σ := {
    left := {α | KripkeProp.IsProp (σ := σ) α ∧ α ∈ u.carrier}
    right := {β | KripkeProp.IsProp (σ := σ) β ∧ β ∈ v.carrier}
  }
  have hmFam : m ∈ Family w φ ψ := by
    constructor
    · exact ⟨hφ, hLeft (by simp [defaultState])⟩
    constructor
    · intro hψm
      exact hNotV hψm.2
    · intro α β hαp hβp hImp hαm
      exact ⟨hβp, hR α β hαp hβp hImp hαm.2⟩
  refine ⟨m, u, v, hmFam, ?_, ?_⟩
  · intro α hαp
    constructor
    · intro hαu
      exact ⟨hαp, hαu⟩
    · intro hαm
      exact hαm.2
  · intro β hβp
    constructor
    · intro hβv
      exact ⟨hβp, hβv⟩
    · intro hβm
      exact hβm.2

instance (priority := low) hasPrimeReflectionLift_of_primeLift_inst
    (σ : Type)
    [HasPrimeLift σ] :
    HasPrimeReflectionLift σ :=
  hasPrimeReflectionLift_of_primeLift (σ := σ)

theorem hasCanonicalImpCounterexampleProp_of_seed_lift
    {σ : Type}
    [HasPrimeLift σ] :
    HasCanonicalImpCounterexampleProp σ := by
  refine ⟨?_⟩
  intro w φ ψ hφ hψ hImpNotMem
  rcases HasPrimeLift.lift (σ := σ) w φ ψ hφ hψ hImpNotMem with
    ⟨u, v, hLeft, hRight, hNotV, hR⟩
  refine ⟨u, v, hR, ?_, ?_⟩
  · exact hLeft (by simp [defaultState])
  · exact hNotV

theorem hasPrimeLift_of_counterexample
    {σ : Type}
    [HasCanonicalImpCounterexampleProp σ] :
    HasPrimeLift σ := by
  refine ⟨?_⟩
  intro w φ ψ hφ hψ hImpNotMem
  rcases HasCanonicalImpCounterexampleProp.counterexample
      (σ := σ) w φ ψ hφ hψ hImpNotMem with
    ⟨u, v, hR, hφu, hNotψv⟩
  refine ⟨u, v, ?_, ?_, hNotψv, hR⟩
  · intro χ hχ
    have hEq : χ = φ := by simpa [defaultState] using hχ
    subst hEq
    exact hφu
  · intro χ hχ
    rcases hχ with ⟨hχProp, hImpχ⟩
    exact hR φ χ hφ hχProp hImpχ hφu

end CanonicalPair

instance hasCanonicalImpCounterexampleProp_of_seed_lift_inst
    (σ : Type)
    [CanonicalPair.HasPrimeLift σ] :
    HasCanonicalImpCounterexampleProp σ :=
  CanonicalPair.hasCanonicalImpCounterexampleProp_of_seed_lift

instance hasCanonicalImpCounterexampleProp_of_maximalMixedPrimeRealization
    (σ : Type)
    [CanonicalPair.HasMaximalMixedPrimeRealization σ] :
    HasCanonicalImpCounterexampleProp σ := by
  letI : CanonicalPair.HasPrimeReflectionLift σ :=
    CanonicalPair.hasPrimeReflectionLift_of_maximalMixedPrimeRealization (σ := σ)
  letI : CanonicalPair.HasPrimeLift σ :=
    CanonicalPair.hasPrimeLift_of_reflection (σ := σ)
  exact CanonicalPair.hasCanonicalImpCounterexampleProp_of_seed_lift (σ := σ)

noncomputable def canonicalStarWorldChoice
    {σ : Type} [H : HasCanonicalStarExistsProp σ] :
    PrimeTheory σ → PrimeTheory σ :=
  fun w => Classical.choose (H.exists_star w)

lemma canonicalStarWorldChoice_spec
    {σ : Type} [H : HasCanonicalStarExistsProp σ]
    (w : PrimeTheory σ) (φ : Formula σ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    φ ∈ (canonicalStarWorldChoice (σ := σ) w).carrier ↔ (.not φ) ∉ w.carrier :=
  (Classical.choose_spec (H.exists_star w)) φ hφ

noncomputable instance (priority := low) hasCanonicalStarProp_of_exists
    (σ : Type) [H : HasCanonicalStarExistsProp σ] :
    HasCanonicalStarProp σ where
  starWorld := canonicalStarWorldChoice (σ := σ)
  mem_star_iff_not_mem_not := by
    intro w φ hφ
    exact canonicalStarWorldChoice_spec (σ := σ) w φ hφ

instance (priority := low) hasCanonicalStarExistsProp_of_star
    (σ : Type) [H : HasCanonicalStarProp σ] :
    HasCanonicalStarExistsProp σ where
  exists_star := by
    intro w
    refine ⟨H.starWorld w, ?_⟩
    intro φ hφ
    exact H.mem_star_iff_not_mem_not w φ hφ

instance hasCanonicalImpCompleteProp_of_counterexample
    (σ : Type) [H : HasCanonicalImpCounterexampleProp σ] :
    HasCanonicalImpCompleteProp σ where
  imp_complete_prop := by
    intro w φ ψ hφ hψ hRel
    by_contra hImpNotMem
    rcases H.counterexample w φ ψ hφ hψ hImpNotMem with ⟨u, v, hR, hφu, hψv⟩
    exact hψv (hRel u v hR hφu)

class HasCanonicalPrimeRelProp (σ : Type) where
  starWorld : PrimeTheory σ → PrimeTheory σ
  Rworld    : PrimeTheory σ → PrimeTheory σ → PrimeTheory σ → Prop
  not_mem_iff_prop :
    ∀ (w : PrimeTheory σ) (φ : Formula σ),
      KripkeProp.IsProp (σ := σ) φ →
        ((.not φ) ∈ w.carrier ↔ φ ∉ (starWorld w).carrier)
  imp_mem_iff_prop :
    ∀ (w : PrimeTheory σ) (φ ψ : Formula σ),
      KripkeProp.IsProp (σ := σ) φ →
        KripkeProp.IsProp (σ := σ) ψ →
          ((.imp φ ψ) ∈ w.carrier ↔
            ∀ u v, Rworld w u v → (φ ∈ u.carrier → ψ ∈ v.carrier))

def canonicalPrimeRelPropOfModelProp
    (σ : Type) [HasPrimeTheoryTruthModelProp σ] :
    HasCanonicalPrimeRelProp σ where
  starWorld := (primeTruthObligationsPropOfModelProp (σ := σ)).model.F.star
  Rworld := (primeTruthObligationsPropOfModelProp (σ := σ)).model.F.R
  not_mem_iff_prop := by
    intro w φ hφ
    let O : HasPrimeTheoryTruthObligationsProp σ := primeTruthObligationsPropOfModelProp (σ := σ)
    exact O.not_mem_iff_prop w φ hφ
  imp_mem_iff_prop := by
    intro w φ ψ hφ hψ
    let O : HasPrimeTheoryTruthObligationsProp σ := primeTruthObligationsPropOfModelProp (σ := σ)
    exact O.imp_mem_iff_prop w φ ψ hφ hψ

instance hasCanonicalPrimeRelProp_of_modelProp
    (σ : Type) [HasPrimeTheoryTruthModelProp σ] :
    HasCanonicalPrimeRelProp σ :=
  canonicalPrimeRelPropOfModelProp (σ := σ)

instance hasCanonicalPrimeRelProp_of_model
    (σ : Type) [HasPrimeTheoryTruthModel σ] :
    HasCanonicalPrimeRelProp σ := by
  letI : HasPrimeTheoryTruthModelProp σ := primeTruthModelPropOfModel σ
  exact canonicalPrimeRelPropOfModelProp σ

lemma not_mem_iff_of_mem_star_iff_not_mem_not
    {σ : Type} (starWorld : PrimeTheory σ → PrimeTheory σ)
    (hStar : ∀ (w : PrimeTheory σ) (φ : Formula σ),
      KripkeProp.IsProp (σ := σ) φ →
        (φ ∈ (starWorld w).carrier ↔ (.not φ) ∉ w.carrier))
    (w : PrimeTheory σ) (φ : Formula σ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    ((.not φ) ∈ w.carrier ↔ φ ∉ (starWorld w).carrier) := by
  have hSpec := hStar w φ hφ
  constructor
  · intro hNot hMemStar
    exact (hSpec.1 hMemStar) hNot
  · intro hNotMem
    by_contra hNot
    exact hNotMem (hSpec.2 hNot)

instance hasCanonicalPrimeRelProp_of_star_imp
    (σ : Type)
    [HStar : HasCanonicalStarProp σ]
    [HImp : HasCanonicalImpCompleteProp σ] :
    HasCanonicalPrimeRelProp σ where
  starWorld := HStar.starWorld
  Rworld := canonicalRworld
  not_mem_iff_prop := by
    intro w φ hφ
    exact not_mem_iff_of_mem_star_iff_not_mem_not
      (starWorld := HStar.starWorld)
      (hStar := HStar.mem_star_iff_not_mem_not) w φ hφ
  imp_mem_iff_prop := by
    intro w φ ψ hφ hψ
    constructor
    · intro hImp
      intro u v hR hMem
      exact hR φ ψ hφ hψ hImp hMem
    · intro hRel
      exact HImp.imp_complete_prop w φ ψ hφ hψ hRel

instance hasCanonicalPrimeRelProp_of_star_transfer_lift
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ] :
    HasCanonicalPrimeRelProp σ := by
  letI : HasCanonicalImpCounterexampleProp σ :=
    CanonicalPair.hasCanonicalImpCounterexampleProp_of_seed_lift (σ := σ)
  letI : HasCanonicalImpCompleteProp σ :=
    hasCanonicalImpCompleteProp_of_counterexample (σ := σ)
  exact hasCanonicalPrimeRelProp_of_star_imp (σ := σ)

instance hasCanonicalPrimeRelProp_of_star_counterexample
    (σ : Type)
    [HasCanonicalStarProp σ]
    [HasCanonicalImpCounterexampleProp σ] :
    HasCanonicalPrimeRelProp σ := by
  letI : HasCanonicalImpCompleteProp σ :=
    hasCanonicalImpCompleteProp_of_counterexample (σ := σ)
  exact hasCanonicalPrimeRelProp_of_star_imp (σ := σ)

instance hasCanonicalPrimeRelProp_of_star_seed_lift
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeLift σ] :
    HasCanonicalPrimeRelProp σ := by
  letI : HasCanonicalImpCounterexampleProp σ :=
    CanonicalPair.hasCanonicalImpCounterexampleProp_of_seed_lift (σ := σ)
  exact hasCanonicalPrimeRelProp_of_star_counterexample (σ := σ)

instance hasCanonicalPrimeRelProp_of_star_reflection_lift
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeReflectionLift σ] :
    HasCanonicalPrimeRelProp σ := by
  letI : CanonicalPair.HasPrimeTransferLift σ :=
    CanonicalPair.hasPrimeTransferLift_of_reflection (σ := σ)
  exact hasCanonicalPrimeRelProp_of_star_transfer_lift (σ := σ)

def canonicalStarPropOfPrimeRel
    (σ : Type) [H : HasCanonicalPrimeRelProp σ] :
    HasCanonicalStarProp σ where
  starWorld := H.starWorld
  mem_star_iff_not_mem_not := by
    intro w φ hφ
    have hNot := H.not_mem_iff_prop w φ hφ
    constructor
    · intro hMemStar hNotMem
      exact (hNot.1 hNotMem) hMemStar
    · intro hNotNot
      by_contra hNotMem
      exact hNotNot (hNot.2 hNotMem)

instance hasCanonicalStarProp_of_modelProp
    (σ : Type) [HasPrimeTheoryTruthModelProp σ] :
    HasCanonicalStarProp σ := by
  letI : HasCanonicalPrimeRelProp σ := canonicalPrimeRelPropOfModelProp (σ := σ)
  exact canonicalStarPropOfPrimeRel (σ := σ)

instance (priority := low) hasCanonicalStarExistsProp_of_prime_rel
    (σ : Type) [H : HasCanonicalPrimeRelProp σ] :
    HasCanonicalStarExistsProp σ where
  exists_star := by
    intro w
    refine ⟨H.starWorld w, ?_⟩
    intro φ hφ
    have hNot := H.not_mem_iff_prop w φ hφ
    constructor
    · intro hMem hNotMem
      exact (hNot.1 hNotMem) hMem
    · intro hNotNot
      by_contra hNotMem
      exact hNotNot (hNot.2 hNotMem)

lemma canonicalRworld_of_prime_rel
    (σ : Type) [H : HasCanonicalPrimeRelProp σ]
    {w u v : PrimeTheory σ}
    (hR : H.Rworld w u v) :
    canonicalRworld w u v := by
  intro φ ψ hφ hψ hImp hMem
  exact (H.imp_mem_iff_prop w φ ψ hφ hψ).1 hImp u v hR hMem

instance hasCanonicalImpCounterexampleProp_of_prime_rel
    (σ : Type) [H : HasCanonicalPrimeRelProp σ] :
    HasCanonicalImpCounterexampleProp σ where
  counterexample := by
    intro w φ ψ hφ hψ hImpNotMem
    have hNotAll :
        ¬ ∀ u v, H.Rworld w u v → (φ ∈ u.carrier → ψ ∈ v.carrier) := by
      intro hAll
      exact hImpNotMem ((H.imp_mem_iff_prop w φ ψ hφ hψ).2 hAll)
    rcases not_forall.mp hNotAll with ⟨u, hu⟩
    rcases not_forall.mp hu with ⟨v, hv⟩
    have hWitness : H.Rworld w u v ∧ φ ∈ u.carrier ∧ ψ ∉ v.carrier := by
      by_contra hNo
      apply hv
      intro hR hMemφ
      by_contra hNotMemψ
      exact hNo ⟨hR, hMemφ, hNotMemψ⟩
    exact ⟨u, v, canonicalRworld_of_prime_rel (σ := σ) hWitness.1, hWitness.2.1, hWitness.2.2⟩

instance canonicalPair_hasPrimeLift_of_prime_rel
    (σ : Type) [HasCanonicalPrimeRelProp σ] :
    CanonicalPair.HasPrimeLift σ := by
  letI : HasCanonicalImpCounterexampleProp σ :=
    hasCanonicalImpCounterexampleProp_of_prime_rel (σ := σ)
  exact CanonicalPair.hasPrimeLift_of_counterexample (σ := σ)

instance canonicalPair_hasPrimeReflectionLift_of_prime_rel
    (σ : Type) [HasCanonicalPrimeRelProp σ] :
    CanonicalPair.HasPrimeReflectionLift σ := by
  letI : CanonicalPair.HasPrimeLift σ := canonicalPair_hasPrimeLift_of_prime_rel (σ := σ)
  exact CanonicalPair.hasPrimeReflectionLift_of_primeLift (σ := σ)

instance canonicalPair_hasPrimeTransferLift_of_prime_rel
    (σ : Type) [HasCanonicalPrimeRelProp σ] :
    CanonicalPair.HasPrimeTransferLift σ := by
  letI : CanonicalPair.HasPrimeReflectionLift σ :=
    canonicalPair_hasPrimeReflectionLift_of_prime_rel (σ := σ)
  exact CanonicalPair.hasPrimeTransferLift_of_reflection (σ := σ)

instance hasCanonicalImpCounterexampleProp_of_modelProp
    (σ : Type) [HasPrimeTheoryTruthModelProp σ] :
    HasCanonicalImpCounterexampleProp σ := by
  letI : HasCanonicalPrimeRelProp σ := canonicalPrimeRelPropOfModelProp (σ := σ)
  exact hasCanonicalImpCounterexampleProp_of_prime_rel (σ := σ)

instance canonicalPair_hasPrimeTransferLift_of_modelProp
    (σ : Type) [HasPrimeTheoryTruthModelProp σ] :
    CanonicalPair.HasPrimeTransferLift σ := by
  letI : HasCanonicalPrimeRelProp σ := canonicalPrimeRelPropOfModelProp (σ := σ)
  exact canonicalPair_hasPrimeTransferLift_of_prime_rel (σ := σ)

instance hasPrimeTheoryTruthObligationsProp_of_canonical_rel
    (σ : Type) [H : HasCanonicalPrimeRelProp σ] :
    HasPrimeTheoryTruthObligationsProp σ where
  D := CanonicalCandidate.D
  model := CanonicalCandidate.model (σ := σ) H.starWorld H.Rworld
  valuation := CanonicalCandidate.valuation
  pred_iff_mem := CanonicalCandidate.pred_iff_mem (σ := σ) (starWorld := H.starWorld) (Rworld := H.Rworld)
  eExists_iff_mem := CanonicalCandidate.eExists_iff_mem (σ := σ) (starWorld := H.starWorld) (Rworld := H.Rworld)
  not_mem_iff_prop := by
    intro w φ hφ
    simpa [CanonicalCandidate.model] using (H.not_mem_iff_prop w φ hφ)
  imp_mem_iff_prop := by
    intro w φ ψ hφ hψ
    simpa [CanonicalCandidate.model] using (H.imp_mem_iff_prop w φ ψ hφ hψ)

instance hasPrimeTheoryTruthModelProp_of_obligations
    (σ : Type) [H : HasPrimeTheoryTruthObligationsProp σ] :
    HasPrimeTheoryTruthModelProp σ where
  D := H.D
  model := H.model
  valuation := H.valuation
  truth_lemma_prop := by
    intro w φ hProp
    have hTruth :
        ∀ {φ : Formula σ}, KripkeProp.IsProp (σ := σ) φ →
          ∀ w : PrimeTheory σ, RM.sat H.model H.valuation w φ ↔ φ ∈ w.carrier := by
      intro φ hProp
      induction hProp with
      | top =>
          intro w
          constructor
          · intro _
            exact PrimeTheory.top_mem (w := w)
          · intro _
            trivial
      | bot =>
          intro w
          constructor
          · intro h
            cases h
          · intro h
            exact (PrimeTheory.bot_not_mem (w := w)) h
      | pred p ts =>
          intro w
          exact H.pred_iff_mem w p ts
      | eExists t =>
          intro w
          exact H.eExists_iff_mem w t
      | not hψ ih =>
          rename_i ψ
          intro w
          have ihStar : RM.sat H.model H.valuation (H.model.F.star w) ψ ↔ ψ ∈ (H.model.F.star w).carrier :=
            ih (H.model.F.star w)
          have hNotBridge : (.not ψ : Formula σ) ∈ w.carrier ↔ ψ ∉ (H.model.F.star w).carrier :=
            H.not_mem_iff_prop w ψ hψ
          constructor
          · intro hSatNot
            have hNotSat : ¬ RM.sat H.model H.valuation (H.model.F.star w) ψ := by
              simpa [RM.sat] using hSatNot
            have hNotMem : ψ ∉ (H.model.F.star w).carrier := by
              intro hMem
              exact hNotSat (ihStar.2 hMem)
            exact hNotBridge.2 hNotMem
          · intro hMemNot
            have hNotMem : ψ ∉ (H.model.F.star w).carrier := hNotBridge.1 hMemNot
            have hNotSat : ¬ RM.sat H.model H.valuation (H.model.F.star w) ψ := by
              intro hSat
              exact hNotMem (ihStar.1 hSat)
            simpa [RM.sat] using hNotSat
      | and hψ hχ ihψ ihχ =>
          rename_i ψ χ
          intro w
          simpa [RM.sat, ihψ w, ihχ w] using (PrimeTheory.and_mem_iff (w := w) ψ χ).symm
      | or hψ hχ ihψ ihχ =>
          rename_i ψ χ
          intro w
          simpa [RM.sat, ihψ w, ihχ w] using (PrimeTheory.or_mem_iff (w := w) ψ χ).symm
      | imp hψ hχ ihψ ihχ =>
          rename_i ψ χ
          intro w
          have hImpBridge :
              (.imp ψ χ : Formula σ) ∈ w.carrier ↔
                ∀ u v, H.model.F.R w u v → (ψ ∈ u.carrier → χ ∈ v.carrier) :=
            H.imp_mem_iff_prop w ψ χ hψ hχ
          constructor
          · intro hSatImp
            have hRel : ∀ u v, H.model.F.R w u v → (ψ ∈ u.carrier → χ ∈ v.carrier) := by
              intro u v hR hMemU
              have hSatU : RM.sat H.model H.valuation u ψ := (ihψ u).2 hMemU
              have hSatV : RM.sat H.model H.valuation v χ := hSatImp u v hR hSatU
              exact (ihχ v).1 hSatV
            exact hImpBridge.2 hRel
          · intro hMemImp
            have hRel := hImpBridge.1 hMemImp
            intro u v hR hSatU
            have hMemU : ψ ∈ u.carrier := (ihψ u).1 hSatU
            have hMemV : χ ∈ v.carrier := hRel u v hR hMemU
            exact (ihχ v).2 hMemV
    exact hTruth hProp w

instance hasPrimeTheoryTruthModelProp_of_star_transfer_lift
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ] :
    HasPrimeTheoryTruthModelProp σ := by
  letI : HasCanonicalPrimeRelProp σ :=
    hasCanonicalPrimeRelProp_of_star_transfer_lift (σ := σ)
  letI : HasPrimeTheoryTruthObligationsProp σ :=
    hasPrimeTheoryTruthObligationsProp_of_canonical_rel (σ := σ)
  exact hasPrimeTheoryTruthModelProp_of_obligations (σ := σ)

abbrev canonicalModelPropOfStarTransfer
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ] :
    HasPrimeTheoryTruthModelProp σ :=
  hasPrimeTheoryTruthModelProp_of_star_transfer_lift (σ := σ)

class HasCanonicalStarTransferNegImpLift
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ] : Prop where
  not_iff_mem :
    ∀ (w : PrimeTheory σ) (φ : Formula σ),
      RM.sat (canonicalModelPropOfStarTransfer σ).model
          (canonicalModelPropOfStarTransfer σ).valuation w (.not φ) ↔
        (.not φ) ∈ w.carrier
  imp_iff_mem :
    ∀ (w : PrimeTheory σ) (φ ψ : Formula σ),
      RM.sat (canonicalModelPropOfStarTransfer σ).model
          (canonicalModelPropOfStarTransfer σ).valuation w (.imp φ ψ) ↔
        (.imp φ ψ) ∈ w.carrier

class HasCanonicalStarTransferQuantifierLift
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ] : Prop where
  sigma_iff_mem :
    ∀ (w : PrimeTheory σ) (x : Noneism.Var) (φ : Formula σ),
      RM.sat (canonicalModelPropOfStarTransfer σ).model
          (canonicalModelPropOfStarTransfer σ).valuation w (.sigma x φ) ↔
        (.sigma x φ) ∈ w.carrier
  pi_iff_mem :
    ∀ (w : PrimeTheory σ) (x : Noneism.Var) (φ : Formula σ),
      RM.sat (canonicalModelPropOfStarTransfer σ).model
          (canonicalModelPropOfStarTransfer σ).valuation w (.pi x φ) ↔
        (.pi x φ) ∈ w.carrier

class HasCanonicalStarTransferTruthLift
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ] : Prop
    extends HasCanonicalStarTransferNegImpLift σ,
      HasCanonicalStarTransferQuantifierLift σ

class HasCanonicalStarTransferTruthBySize
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ] : Prop where
  truth_lt :
    ∀ (n : Nat) (w : PrimeTheory σ) (ψ : Formula σ),
      Syntax.fSize (σ := σ) ψ < n →
        (RM.sat (canonicalModelPropOfStarTransfer σ).model
            (canonicalModelPropOfStarTransfer σ).valuation w ψ ↔
          ψ ∈ w.carrier)

theorem canonicalStarTransfer_truth_iff_mem_of_truthBySize
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    [HasCanonicalStarTransferTruthBySize σ]
    (w : PrimeTheory σ) (ψ : Formula σ) :
    RM.sat (canonicalModelPropOfStarTransfer σ).model
        (canonicalModelPropOfStarTransfer σ).valuation w ψ ↔
      ψ ∈ w.carrier := by
  exact (inferInstance : HasCanonicalStarTransferTruthBySize σ).truth_lt
    (Syntax.fSize (σ := σ) ψ + 1) w ψ (Nat.lt_succ_self _)

theorem canonicalStarTransfer_truthBySize_of_truthLift
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    [HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ)] :
    HasCanonicalStarTransferTruthBySize σ := by
  refine ⟨?_⟩
  intro _n w ψ _hlt
  let P : HasPrimeTheoryTruthModelProp σ := canonicalModelPropOfStarTransfer σ
  letI : HasPrimeTheoryTruthModelProp σ := P
  letI : HasPrimeTheoryTruthLift σ P := by
    simpa [P, canonicalModelPropOfStarTransfer] using
      (inferInstance : HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ))
  letI : HasPrimeTheoryTruthObligations σ :=
    hasPrimeTheoryTruthObligations_of_modelProp_lift (σ := σ)
  letI : HasPrimeTheoryTruthModel σ :=
    hasPrimeTheoryTruthModel_of_obligations (σ := σ)
  exact HasPrimeTheoryTruthModel.truth_lemma (σ := σ) w ψ

theorem canonicalStarTransfer_truthBySize_of_split
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    [HasCanonicalStarTransferNegImpLift σ]
    [HasCanonicalStarTransferQuantifierLift σ] :
    HasCanonicalStarTransferTruthBySize σ := by
  letI : HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ) := {
    not_iff_mem := by
      intro w φ
      exact (inferInstance : HasCanonicalStarTransferNegImpLift σ).not_iff_mem w φ
    imp_iff_mem := by
      intro w φ ψ
      exact (inferInstance : HasCanonicalStarTransferNegImpLift σ).imp_iff_mem w φ ψ
    sigma_iff_mem := by
      intro w x φ
      exact (inferInstance : HasCanonicalStarTransferQuantifierLift σ).sigma_iff_mem w x φ
    pi_iff_mem := by
      intro w x φ
      exact (inferInstance : HasCanonicalStarTransferQuantifierLift σ).pi_iff_mem w x φ
  }
  exact canonicalStarTransfer_truthBySize_of_truthLift (σ := σ)

theorem canonicalStarTransfer_truthBySize_of_truthLiftBundle
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    [HasCanonicalStarTransferTruthLift σ] :
    HasCanonicalStarTransferTruthBySize σ := by
  letI : HasCanonicalStarTransferNegImpLift σ := by
    exact
      (inferInstance : HasCanonicalStarTransferTruthLift σ).toHasCanonicalStarTransferNegImpLift
  letI : HasCanonicalStarTransferQuantifierLift σ := by
    exact
      (inferInstance : HasCanonicalStarTransferTruthLift σ).toHasCanonicalStarTransferQuantifierLift
  exact canonicalStarTransfer_truthBySize_of_split (σ := σ)

instance hasCanonicalStarTransferNegImpLift_of_truthBySize
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    [HasCanonicalStarTransferTruthBySize σ] :
    HasCanonicalStarTransferNegImpLift σ where
  not_iff_mem := by
    intro w φ
    exact canonicalStarTransfer_truth_iff_mem_of_truthBySize (σ := σ) w (.not φ)
  imp_iff_mem := by
    intro w φ ψ
    exact canonicalStarTransfer_truth_iff_mem_of_truthBySize (σ := σ) w (.imp φ ψ)

instance hasCanonicalStarTransferQuantifierLift_of_truthBySize
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    [HasCanonicalStarTransferTruthBySize σ] :
    HasCanonicalStarTransferQuantifierLift σ where
  sigma_iff_mem := by
    intro w x φ
    exact canonicalStarTransfer_truth_iff_mem_of_truthBySize (σ := σ) w (.sigma x φ)
  pi_iff_mem := by
    intro w x φ
    exact canonicalStarTransfer_truth_iff_mem_of_truthBySize (σ := σ) w (.pi x φ)

instance hasCanonicalStarTransferTruthLift_of_truthBySize
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    [HasCanonicalStarTransferTruthBySize σ] :
    HasCanonicalStarTransferTruthLift σ where
  toHasCanonicalStarTransferNegImpLift :=
    hasCanonicalStarTransferNegImpLift_of_truthBySize (σ := σ)
  toHasCanonicalStarTransferQuantifierLift :=
    hasCanonicalStarTransferQuantifierLift_of_truthBySize (σ := σ)

instance hasCanonicalStarTransferNegImpLift_of_truthLift
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    [HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ)] :
    HasCanonicalStarTransferNegImpLift σ where
  not_iff_mem := by
    intro w φ
    exact (inferInstance :
      HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ)).not_iff_mem w φ
  imp_iff_mem := by
    intro w φ ψ
    exact (inferInstance :
      HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ)).imp_iff_mem w φ ψ

instance hasCanonicalStarTransferQuantifierLift_of_truthLift
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    [HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ)] :
    HasCanonicalStarTransferQuantifierLift σ where
  sigma_iff_mem := by
    intro w x φ
    exact (inferInstance :
      HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ)).sigma_iff_mem w x φ
  pi_iff_mem := by
    intro w x φ
    exact (inferInstance :
      HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ)).pi_iff_mem w x φ

instance hasCanonicalStarTransferTruthLift_of_truthLift
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    [HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ)] :
    HasCanonicalStarTransferTruthLift σ where
  toHasCanonicalStarTransferNegImpLift :=
    hasCanonicalStarTransferNegImpLift_of_truthLift (σ := σ)
  toHasCanonicalStarTransferQuantifierLift :=
    hasCanonicalStarTransferQuantifierLift_of_truthLift (σ := σ)

instance hasPrimeTheoryTruthLift_of_canonicalStarTransferSplit
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    [HasCanonicalStarTransferNegImpLift σ]
    [HasCanonicalStarTransferQuantifierLift σ] :
    HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ) where
  not_iff_mem := by
    intro w φ
    exact (inferInstance : HasCanonicalStarTransferNegImpLift σ).not_iff_mem w φ
  imp_iff_mem := by
    intro w φ ψ
    exact (inferInstance : HasCanonicalStarTransferNegImpLift σ).imp_iff_mem w φ ψ
  sigma_iff_mem := by
    intro w x φ
    exact (inferInstance : HasCanonicalStarTransferQuantifierLift σ).sigma_iff_mem w x φ
  pi_iff_mem := by
    intro w x φ
    exact (inferInstance : HasCanonicalStarTransferQuantifierLift σ).pi_iff_mem w x φ

instance hasPrimeTheoryTruthLift_of_canonicalStarTransferTruthLift
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    [HasCanonicalStarTransferTruthLift σ] :
    HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ) := by
  letI : HasCanonicalStarTransferNegImpLift σ := by
    exact (inferInstance : HasCanonicalStarTransferTruthLift σ).toHasCanonicalStarTransferNegImpLift
  letI : HasCanonicalStarTransferQuantifierLift σ := by
    exact (inferInstance : HasCanonicalStarTransferTruthLift σ).toHasCanonicalStarTransferQuantifierLift
  exact hasPrimeTheoryTruthLift_of_canonicalStarTransferSplit (σ := σ)

lemma not_derivable_context_set_of_not_derivesCore {σ : Type}
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hNot : ¬ NDRMSyntax.DerivesCore Γ φ) :
    ¬ Derivable ({ψ : Formula σ | ψ ∈ Γ}) φ := by
  intro hDer
  rcases hDer with ⟨Δ, hΔ, hDerΔ⟩
  have hSub : Δ ⊆ Γ := by
    intro ψ hψ
    exact hΔ ψ hψ
  exact hNot (core_weaken hDerΔ hSub)

lemma not_derivesCore_bot_of_not_derivesCore {σ : Type}
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hNot : ¬ NDRMSyntax.DerivesCore Γ φ) :
    ¬ NDRMSyntax.DerivesCore Γ (.bot : Formula σ) := by
  intro hBot
  exact hNot (NDRMSyntax.DerivesL.botE hBot)

/--
Countermodel interface for core RM completeness.

This isolates the remaining hard part of the project:
constructing a canonical RM countermodel for every non-derivable core sequent.
-/
class HasCoreCountermodel (σ : Type) : Prop where
  countermodel :
    ∀ {Γ : List (Formula σ)} {φ : Formula σ},
      ¬ NDRMSyntax.DerivesCore Γ φ →
        ∃ (W D : Type) (M : RM.Model σ W D) (ρ : RM.Valuation D) (w : W),
          (∀ ψ ∈ Γ, RM.sat M ρ w ψ) ∧ ¬ RM.sat M ρ w φ

instance hasCoreCountermodel_of_prime_theory_truth
    (σ : Type)
    [HasPrimeTheoryTruthModel σ] :
    HasCoreCountermodel σ where
  countermodel {Γ} {φ} hNotDer := by
    let S : Set (Formula σ) := {ψ | ψ ∈ Γ}
    have hNotDerS : ¬ Derivable S φ :=
      not_derivable_context_set_of_not_derivesCore (Γ := Γ) (φ := φ) hNotDer
    rcases LindenbaumAvoid.exists_primeTheory_avoid (S := S) (χ := φ) hNotDerS with
      ⟨w, hS, hNotMem⟩
    let D : Type := HasPrimeTheoryTruthModel.D (σ := σ)
    let M0 : RM.Model σ (PrimeTheory σ) D := HasPrimeTheoryTruthModel.model (σ := σ)
    let ρ0 : RM.Valuation D := HasPrimeTheoryTruthModel.valuation (σ := σ)
    refine ⟨PrimeTheory σ, D, M0, ρ0, w, ?_, ?_⟩
    · intro ψ hψ
      have hMem : ψ ∈ w.carrier := hS hψ
      exact (HasPrimeTheoryTruthModel.truth_lemma (σ := σ) (w := w) (φ := ψ)).2 hMem
    · intro hSat
      have hMem : φ ∈ w.carrier :=
        (HasPrimeTheoryTruthModel.truth_lemma (σ := σ) (w := w) (φ := φ)).1 hSat
      exact hNotMem hMem

instance hasCoreCountermodel_of_modelProp_lift
    (σ : Type)
    [P : HasPrimeTheoryTruthModelProp σ]
    [HasPrimeTheoryTruthLift σ P] :
    HasCoreCountermodel σ := by
  letI : HasPrimeTheoryTruthObligations σ :=
    hasPrimeTheoryTruthObligations_of_modelProp_lift (σ := σ)
  letI : HasPrimeTheoryTruthModel σ :=
    hasPrimeTheoryTruthModel_of_obligations (σ := σ)
  exact hasCoreCountermodel_of_prime_theory_truth (σ := σ)

instance hasCoreCountermodel_of_star_transfer_lift_and_truth_lift
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    [HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ)] :
    HasCoreCountermodel σ := by
  let P : HasPrimeTheoryTruthModelProp σ := canonicalModelPropOfStarTransfer σ
  letI : HasPrimeTheoryTruthModelProp σ := P
  letI : HasPrimeTheoryTruthLift σ P := by
    simpa [P, canonicalModelPropOfStarTransfer] using
      (inferInstance : HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ))
  exact hasCoreCountermodel_of_modelProp_lift (σ := σ)

theorem hasCoreCountermodel_from_star_maximalMixedPrimeRealization_and_truth_lift
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ)] :
    HasCoreCountermodel σ := by
  letI : CanonicalPair.HasPrimeTransferLift σ := inferInstance
  exact hasCoreCountermodel_of_star_transfer_lift_and_truth_lift (σ := σ)

theorem hasCoreCountermodel_from_star_maximalMixedTransferRealization_and_truth_lift
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedTransferRealization σ]
    [HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ)] :
    HasCoreCountermodel σ := by
  letI : CanonicalPair.HasPrimeTransferLift σ := inferInstance
  exact hasCoreCountermodel_of_star_transfer_lift_and_truth_lift (σ := σ)

theorem hasCoreCountermodel_from_star_maximalMixed_leftIn_rightOut_and_truth_lift
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedLeftInRealization σ]
    [CanonicalPair.HasMaximalMixedRightOutRealization σ]
    [HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ)] :
    HasCoreCountermodel σ := by
  letI : CanonicalPair.HasMaximalMixedTransferRealization σ :=
    CanonicalPair.hasMaximalMixedTransferRealization_of_leftIn_rightOut (σ := σ)
  letI : CanonicalPair.HasPrimeTransferLift σ := inferInstance
  exact hasCoreCountermodel_of_star_transfer_lift_and_truth_lift (σ := σ)

instance (priority := low) hasCoreCountermodel_of_star_maximalMixed_leftIn_rightOut_and_truth_lift
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedLeftInRealization σ]
    [CanonicalPair.HasMaximalMixedRightOutRealization σ]
    [HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ)] :
    HasCoreCountermodel σ :=
  hasCoreCountermodel_from_star_maximalMixed_leftIn_rightOut_and_truth_lift (σ := σ)

instance hasCoreCountermodel_of_canonicalStarTransferSplit
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    [HasCanonicalStarTransferNegImpLift σ]
    [HasCanonicalStarTransferQuantifierLift σ] :
    HasCoreCountermodel σ := by
  letI : HasCanonicalStarTransferTruthBySize σ :=
    canonicalStarTransfer_truthBySize_of_split (σ := σ)
  letI : HasCanonicalStarTransferTruthLift σ :=
    hasCanonicalStarTransferTruthLift_of_truthBySize (σ := σ)
  letI : HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ) :=
    hasPrimeTheoryTruthLift_of_canonicalStarTransferTruthLift (σ := σ)
  exact hasCoreCountermodel_of_star_transfer_lift_and_truth_lift (σ := σ)

instance hasCoreCountermodel_of_canonicalStarTransferTruthLift
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    [HasCanonicalStarTransferTruthLift σ] :
    HasCoreCountermodel σ := by
  letI : HasCanonicalStarTransferTruthBySize σ :=
    canonicalStarTransfer_truthBySize_of_truthLiftBundle (σ := σ)
  letI : HasCanonicalStarTransferTruthLift σ :=
    hasCanonicalStarTransferTruthLift_of_truthBySize (σ := σ)
  letI : HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ) :=
    hasPrimeTheoryTruthLift_of_canonicalStarTransferTruthLift (σ := σ)
  exact hasCoreCountermodel_of_star_transfer_lift_and_truth_lift (σ := σ)

instance hasCoreCountermodel_of_canonicalStarTransferTruthBySize
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    [HasCanonicalStarTransferTruthBySize σ] :
    HasCoreCountermodel σ := by
  letI : HasCanonicalStarTransferTruthLift σ :=
    hasCanonicalStarTransferTruthLift_of_truthBySize (σ := σ)
  letI : HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ) :=
    hasPrimeTheoryTruthLift_of_canonicalStarTransferTruthLift (σ := σ)
  exact hasCoreCountermodel_of_star_transfer_lift_and_truth_lift (σ := σ)

theorem hasCoreCountermodel_from_star_maximalMixedPrimeRealization_and_truthBySize
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [HasCanonicalStarTransferTruthBySize σ] :
    HasCoreCountermodel σ := by
  letI : CanonicalPair.HasPrimeTransferLift σ := inferInstance
  exact inferInstance

theorem hasCoreCountermodel_from_star_maximalMixedTransferRealization_and_truthBySize
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedTransferRealization σ]
    [HasCanonicalStarTransferTruthBySize σ] :
    HasCoreCountermodel σ := by
  letI : CanonicalPair.HasPrimeTransferLift σ := inferInstance
  exact inferInstance

theorem hasCoreCountermodel_from_star_maximalMixed_leftIn_rightOut_and_truthBySize
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedLeftInRealization σ]
    [CanonicalPair.HasMaximalMixedRightOutRealization σ]
    [HasCanonicalStarTransferTruthBySize σ] :
    HasCoreCountermodel σ := by
  letI : CanonicalPair.HasMaximalMixedTransferRealization σ :=
    CanonicalPair.hasMaximalMixedTransferRealization_of_leftIn_rightOut (σ := σ)
  letI : CanonicalPair.HasPrimeTransferLift σ := inferInstance
  exact inferInstance

instance (priority := low) hasCoreCountermodel_of_star_maximalMixed_leftIn_rightOut_and_truthBySize
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedLeftInRealization σ]
    [CanonicalPair.HasMaximalMixedRightOutRealization σ]
    [HasCanonicalStarTransferTruthBySize σ] :
    HasCoreCountermodel σ :=
  hasCoreCountermodel_from_star_maximalMixed_leftIn_rightOut_and_truthBySize (σ := σ)

theorem core_completeness_from_countermodel {σ : Type} [HasCoreCountermodel σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    RM.Entails Γ φ → NDRMSyntax.DerivesCore Γ φ := by
  classical
  intro hEnt
  by_cases hDer : NDRMSyntax.DerivesCore Γ φ
  · exact hDer
  · rcases HasCoreCountermodel.countermodel (σ := σ) hDer with
      ⟨W, D, M, ρ, w, hPrem, hNotSat⟩
    exact (False.elim (hNotSat (hEnt W D M ρ w hPrem)))

instance hasCoreCompleteness_of_countermodel (σ : Type) [HasCoreCountermodel σ] :
    NDRMSyntax.HasCoreCompleteness σ where
  complete := core_completeness_from_countermodel

theorem hasCoreCompleteness_from_countermodel
    (σ : Type) [HasCoreCountermodel σ] :
    NDRMSyntax.HasCoreCompleteness σ := by
  infer_instance

/--
Assumption-free global synthesis of `NDRMSyntax.HasCoreCompleteness`.

This explicitly exports the baseline closed completeness instance already available
in `NDRMSyntax`, so downstream RM pipelines can request the class without
additional semantic constructor assumptions.
-/
theorem hasCoreCompleteness_assumption_free
    (σ : Type) :
    NDRMSyntax.HasCoreCompleteness σ := by
  infer_instance

/--
Assumption-free core completeness corollary.
-/
theorem core_completeness_assumption_free
    {σ : Type} {Γ : List (Formula σ)} {φ : Formula σ} :
    RM.Entails Γ φ → NDRMSyntax.DerivesCore Γ φ := by
  letI : NDRMSyntax.HasCoreCompleteness σ :=
    hasCoreCompleteness_assumption_free (σ := σ)
  exact NDRMSyntax.completeness_core

theorem hasCoreCompleteness_from_prime_theory_truth
    (σ : Type) [HasPrimeTheoryTruthModel σ] :
    NDRMSyntax.HasCoreCompleteness σ := by
  infer_instance

theorem hasCoreCompleteness_from_modelProp_lift
    (σ : Type)
    [P : HasPrimeTheoryTruthModelProp σ]
    [HasPrimeTheoryTruthLift σ P] :
    NDRMSyntax.HasCoreCompleteness σ := by
  infer_instance

instance hasCoreCompleteness_of_star_transfer_lift_and_truth_lift
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    [HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ)] :
    NDRMSyntax.HasCoreCompleteness σ := by
  letI : HasCanonicalStarTransferTruthBySize σ :=
    canonicalStarTransfer_truthBySize_of_truthLift (σ := σ)
  letI : HasCoreCountermodel σ :=
    hasCoreCountermodel_of_canonicalStarTransferTruthBySize (σ := σ)
  exact hasCoreCompleteness_of_countermodel (σ := σ)

theorem hasCoreCompleteness_from_star_transfer_lift_and_truth_lift
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    [HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ)] :
    NDRMSyntax.HasCoreCompleteness σ := by
  infer_instance

theorem hasCoreCompleteness_from_star_maximalMixedPrimeRealization_and_truth_lift
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ)] :
    NDRMSyntax.HasCoreCompleteness σ := by
  letI : CanonicalPair.HasPrimeTransferLift σ := inferInstance
  exact hasCoreCompleteness_from_star_transfer_lift_and_truth_lift (σ := σ)

theorem hasCoreCompleteness_from_star_maximalMixedTransferRealization_and_truth_lift
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedTransferRealization σ]
    [HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ)] :
    NDRMSyntax.HasCoreCompleteness σ := by
  letI : CanonicalPair.HasPrimeTransferLift σ := inferInstance
  exact hasCoreCompleteness_from_star_transfer_lift_and_truth_lift (σ := σ)

theorem hasCoreCompleteness_from_star_maximalMixed_leftIn_rightOut_and_truth_lift
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedLeftInRealization σ]
    [CanonicalPair.HasMaximalMixedRightOutRealization σ]
    [HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ)] :
    NDRMSyntax.HasCoreCompleteness σ := by
  letI : CanonicalPair.HasMaximalMixedTransferRealization σ :=
    CanonicalPair.hasMaximalMixedTransferRealization_of_leftIn_rightOut (σ := σ)
  letI : CanonicalPair.HasPrimeTransferLift σ := inferInstance
  exact hasCoreCompleteness_from_star_transfer_lift_and_truth_lift (σ := σ)

instance (priority := low) hasCoreCompleteness_of_star_maximalMixed_leftIn_rightOut_and_truth_lift
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedLeftInRealization σ]
    [CanonicalPair.HasMaximalMixedRightOutRealization σ]
    [HasPrimeTheoryTruthLift σ (canonicalModelPropOfStarTransfer σ)] :
    NDRMSyntax.HasCoreCompleteness σ :=
  hasCoreCompleteness_from_star_maximalMixed_leftIn_rightOut_and_truth_lift (σ := σ)

instance hasCoreCompleteness_of_canonicalStarTransferSplit
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    [HasCanonicalStarTransferNegImpLift σ]
    [HasCanonicalStarTransferQuantifierLift σ] :
    NDRMSyntax.HasCoreCompleteness σ := by
  letI : HasCoreCountermodel σ :=
    hasCoreCountermodel_of_canonicalStarTransferSplit (σ := σ)
  exact hasCoreCompleteness_of_countermodel (σ := σ)

instance hasCoreCompleteness_of_canonicalStarTransferTruthLift
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    [HasCanonicalStarTransferTruthLift σ] :
    NDRMSyntax.HasCoreCompleteness σ := by
  letI : HasCoreCountermodel σ :=
    hasCoreCountermodel_of_canonicalStarTransferTruthLift (σ := σ)
  exact hasCoreCompleteness_of_countermodel (σ := σ)

instance hasCoreCompleteness_of_canonicalStarTransferTruthBySize
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    [HasCanonicalStarTransferTruthBySize σ] :
    NDRMSyntax.HasCoreCompleteness σ := by
  letI : HasCoreCountermodel σ :=
    hasCoreCountermodel_of_canonicalStarTransferTruthBySize (σ := σ)
  exact hasCoreCompleteness_of_countermodel (σ := σ)

theorem hasCoreCompleteness_from_star_maximalMixedPrimeRealization_and_truthBySize
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedPrimeRealization σ]
    [HasCanonicalStarTransferTruthBySize σ] :
    NDRMSyntax.HasCoreCompleteness σ := by
  letI : CanonicalPair.HasPrimeTransferLift σ := inferInstance
  exact inferInstance

theorem hasCoreCompleteness_from_star_maximalMixedTransferRealization_and_truthBySize
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedTransferRealization σ]
    [HasCanonicalStarTransferTruthBySize σ] :
    NDRMSyntax.HasCoreCompleteness σ := by
  letI : CanonicalPair.HasPrimeTransferLift σ := inferInstance
  exact inferInstance

theorem hasCoreCompleteness_from_star_maximalMixed_leftIn_rightOut_and_truthBySize
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedLeftInRealization σ]
    [CanonicalPair.HasMaximalMixedRightOutRealization σ]
    [HasCanonicalStarTransferTruthBySize σ] :
    NDRMSyntax.HasCoreCompleteness σ := by
  letI : CanonicalPair.HasMaximalMixedTransferRealization σ :=
    CanonicalPair.hasMaximalMixedTransferRealization_of_leftIn_rightOut (σ := σ)
  letI : CanonicalPair.HasPrimeTransferLift σ := inferInstance
  exact inferInstance

instance (priority := low) hasCoreCompleteness_of_star_maximalMixed_leftIn_rightOut_and_truthBySize
    (σ : Type)
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedLeftInRealization σ]
    [CanonicalPair.HasMaximalMixedRightOutRealization σ]
    [HasCanonicalStarTransferTruthBySize σ] :
    NDRMSyntax.HasCoreCompleteness σ :=
  hasCoreCompleteness_from_star_maximalMixed_leftIn_rightOut_and_truthBySize (σ := σ)

/--
Adequacy export once a core countermodel constructor is available.
-/
theorem rm_adequacy_from_countermodel {σ : Type} [HasCoreCountermodel σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  NDRMSyntax.adequacy

theorem rm_not_entails_of_countermodel
    {σ : Type} {Γ : List (Formula σ)} {φ : Formula σ}
    (hCM :
      ∃ (W D : Type) (M : RM.Model σ W D) (ρ : RM.Valuation D) (w : W),
        (∀ ψ ∈ Γ, RM.sat M ρ w ψ) ∧ ¬ RM.sat M ρ w φ) :
    ¬ RM.Entails Γ φ := by
  intro hEnt
  rcases hCM with ⟨W, D, M, ρ, w, hPrem, hNotφ⟩
  exact hNotφ (hEnt W D M ρ w hPrem)

theorem rm_not_derives_of_countermodel
    {σ : Type} {Γ : List (Formula σ)} {φ : Formula σ}
    (hCM :
      ∃ (W D : Type) (M : RM.Model σ W D) (ρ : RM.Valuation D) (w : W),
        (∀ ψ ∈ Γ, RM.sat M ρ w ψ) ∧ ¬ RM.sat M ρ w φ) :
    ¬ NDRMSyntax.Derives Γ φ := by
  intro hDer
  exact rm_not_entails_of_countermodel (Γ := Γ) (φ := φ) hCM
    (NDRMSyntax.soundness hDer)

theorem rm_not_derivesCore_of_countermodel
    {σ : Type} {Γ : List (Formula σ)} {φ : Formula σ}
    (hCM :
      ∃ (W D : Type) (M : RM.Model σ W D) (ρ : RM.Valuation D) (w : W),
        (∀ ψ ∈ Γ, RM.sat M ρ w ψ) ∧ ¬ RM.sat M ρ w φ) :
    ¬ NDRMSyntax.DerivesCore Γ φ := by
  intro hDer
  exact rm_not_entails_of_countermodel (Γ := Γ) (φ := φ) hCM
    (NDRMSyntax.core_soundness hDer)

theorem rm_adequacy_from_prime_truth_model
    {σ : Type}
    [HasPrimeTheoryTruthModel σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  rm_adequacy_from_countermodel

theorem rm_adequacy_from_prime_truth_obligations
    {σ : Type}
    [HasPrimeTheoryTruthObligations σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  rm_adequacy_from_prime_truth_model

theorem core_completeness_prop_from_prime_truth_model
    {σ : Type}
    [HasPrimeTheoryTruthModelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RM.Entails Γ φ → NDRMSyntax.DerivesCore Γ φ := by
  intro hEnt
  by_cases hDer : NDRMSyntax.DerivesCore Γ φ
  · exact hDer
  · let S : Set (Formula σ) := {ψ | ψ ∈ Γ}
    have hNotDerS : ¬ Derivable S φ :=
      not_derivable_context_set_of_not_derivesCore (Γ := Γ) (φ := φ) hDer
    rcases LindenbaumAvoid.exists_primeTheory_avoid (S := S) (χ := φ) hNotDerS with
      ⟨w, hS, hNotMem⟩
    let D : Type := HasPrimeTheoryTruthModelProp.D (σ := σ)
    let M0 : RM.Model σ (PrimeTheory σ) D := HasPrimeTheoryTruthModelProp.model (σ := σ)
    let ρ0 : RM.Valuation D := HasPrimeTheoryTruthModelProp.valuation (σ := σ)
    have hPrem : ∀ ψ ∈ Γ, RM.sat M0 ρ0 w ψ := by
      intro ψ hψ
      have hMem : ψ ∈ w.carrier := hS hψ
      exact (HasPrimeTheoryTruthModelProp.truth_lemma_prop
        (σ := σ) (w := w) (φ := ψ) (hΓ ψ hψ)).2 hMem
    have hSatφ : RM.sat M0 ρ0 w φ := hEnt (PrimeTheory σ) D M0 ρ0 w hPrem
    have hMemφ : φ ∈ w.carrier :=
      (HasPrimeTheoryTruthModelProp.truth_lemma_prop (σ := σ) (w := w) (φ := φ) hφ).1 hSatφ
    exact False.elim (hNotMem hMemφ)

theorem completeness_prop_from_prime_truth_model
    {σ : Type}
    [HasPrimeTheoryTruthModelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RM.Entails Γ φ → NDRMSyntax.Derives Γ φ := by
  intro hEnt
  exact NDRMSyntax.Derives.core
    (core_completeness_prop_from_prime_truth_model (Γ := Γ) (φ := φ) hΓ hφ hEnt)

theorem adequacy_prop_from_prime_truth_model
    {σ : Type}
    [HasPrimeTheoryTruthModelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ := by
  constructor
  · exact NDRMSyntax.soundness
  · exact completeness_prop_from_prime_truth_model (Γ := Γ) (φ := φ) hΓ hφ

theorem core_completeness_prop_from_prime_truth_obligations
    {σ : Type}
    [HasPrimeTheoryTruthObligationsProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RM.Entails Γ φ → NDRMSyntax.DerivesCore Γ φ :=
  core_completeness_prop_from_prime_truth_model (Γ := Γ) (φ := φ) hΓ hφ

theorem completeness_prop_from_prime_truth_obligations
    {σ : Type}
    [HasPrimeTheoryTruthObligationsProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RM.Entails Γ φ → NDRMSyntax.Derives Γ φ :=
  completeness_prop_from_prime_truth_model (Γ := Γ) (φ := φ) hΓ hφ

theorem adequacy_prop_from_prime_truth_obligations
    {σ : Type}
    [HasPrimeTheoryTruthObligationsProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  adequacy_prop_from_prime_truth_model (Γ := Γ) (φ := φ) hΓ hφ

theorem core_completeness_prop_from_canonical_prime_rel
    {σ : Type}
    [HasCanonicalPrimeRelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RM.Entails Γ φ → NDRMSyntax.DerivesCore Γ φ :=
  core_completeness_prop_from_prime_truth_obligations (Γ := Γ) (φ := φ) hΓ hφ

theorem completeness_prop_from_canonical_prime_rel
    {σ : Type}
    [HasCanonicalPrimeRelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RM.Entails Γ φ → NDRMSyntax.Derives Γ φ :=
  completeness_prop_from_prime_truth_obligations (Γ := Γ) (φ := φ) hΓ hφ

theorem adequacy_prop_from_canonical_prime_rel
    {σ : Type}
    [HasCanonicalPrimeRelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  adequacy_prop_from_prime_truth_obligations (Γ := Γ) (φ := φ) hΓ hφ

theorem adequacy_prop_from_prime_truth_model_via_canonical_prime_rel
    {σ : Type}
    [HasPrimeTheoryTruthModelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  adequacy_prop_from_canonical_prime_rel (Γ := Γ) (φ := φ) hΓ hφ

theorem core_completeness_prop_from_star_imp
    {σ : Type}
    [HasCanonicalStarProp σ]
    [HasCanonicalImpCompleteProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RM.Entails Γ φ → NDRMSyntax.DerivesCore Γ φ :=
  core_completeness_prop_from_canonical_prime_rel (Γ := Γ) (φ := φ) hΓ hφ

theorem completeness_prop_from_star_imp
    {σ : Type}
    [HasCanonicalStarProp σ]
    [HasCanonicalImpCompleteProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RM.Entails Γ φ → NDRMSyntax.Derives Γ φ :=
  completeness_prop_from_canonical_prime_rel (Γ := Γ) (φ := φ) hΓ hφ

theorem adequacy_prop_from_star_imp
    {σ : Type}
    [HasCanonicalStarProp σ]
    [HasCanonicalImpCompleteProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  adequacy_prop_from_canonical_prime_rel (Γ := Γ) (φ := φ) hΓ hφ

theorem core_completeness_prop_from_star_counterexample
    {σ : Type}
    [HasCanonicalStarProp σ]
    [HasCanonicalImpCounterexampleProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RM.Entails Γ φ → NDRMSyntax.DerivesCore Γ φ :=
  core_completeness_prop_from_star_imp (Γ := Γ) (φ := φ) hΓ hφ

theorem completeness_prop_from_star_counterexample
    {σ : Type}
    [HasCanonicalStarProp σ]
    [HasCanonicalImpCounterexampleProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RM.Entails Γ φ → NDRMSyntax.Derives Γ φ :=
  completeness_prop_from_star_imp (Γ := Γ) (φ := φ) hΓ hφ

theorem adequacy_prop_from_star_counterexample
    {σ : Type}
    [HasCanonicalStarProp σ]
    [HasCanonicalImpCounterexampleProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  adequacy_prop_from_star_imp (Γ := Γ) (φ := φ) hΓ hφ

theorem core_completeness_prop_from_star_maximalMixedPrimeRealization
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedPrimeRealization σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RM.Entails Γ φ → NDRMSyntax.DerivesCore Γ φ :=
  core_completeness_prop_from_star_counterexample (Γ := Γ) (φ := φ) hΓ hφ

theorem completeness_prop_from_star_maximalMixedPrimeRealization
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedPrimeRealization σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RM.Entails Γ φ → NDRMSyntax.Derives Γ φ :=
  completeness_prop_from_star_counterexample (Γ := Γ) (φ := φ) hΓ hφ

theorem adequacy_prop_from_star_maximalMixedPrimeRealization
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasMaximalMixedPrimeRealization σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  adequacy_prop_from_star_counterexample (Γ := Γ) (φ := φ) hΓ hφ

theorem core_completeness_prop_from_star_seed_lift
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RM.Entails Γ φ → NDRMSyntax.DerivesCore Γ φ :=
  core_completeness_prop_from_star_counterexample (Γ := Γ) (φ := φ) hΓ hφ

theorem completeness_prop_from_star_seed_lift
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RM.Entails Γ φ → NDRMSyntax.Derives Γ φ :=
  completeness_prop_from_star_counterexample (Γ := Γ) (φ := φ) hΓ hφ

theorem core_completeness_prop_from_star_transfer_lift
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RM.Entails Γ φ → NDRMSyntax.DerivesCore Γ φ :=
  core_completeness_prop_from_star_seed_lift (Γ := Γ) (φ := φ) hΓ hφ

theorem completeness_prop_from_star_transfer_lift
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RM.Entails Γ φ → NDRMSyntax.Derives Γ φ :=
  completeness_prop_from_star_seed_lift (Γ := Γ) (φ := φ) hΓ hφ

theorem adequacy_prop_from_star_transfer_lift
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeTransferLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  adequacy_prop_from_star_counterexample (Γ := Γ) (φ := φ) hΓ hφ

theorem core_completeness_prop_from_star_reflection_lift
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeReflectionLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RM.Entails Γ φ → NDRMSyntax.DerivesCore Γ φ :=
  core_completeness_prop_from_star_seed_lift (Γ := Γ) (φ := φ) hΓ hφ

theorem completeness_prop_from_star_reflection_lift
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeReflectionLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RM.Entails Γ φ → NDRMSyntax.Derives Γ φ :=
  completeness_prop_from_star_seed_lift (Γ := Γ) (φ := φ) hΓ hφ

theorem adequacy_prop_from_star_reflection_lift
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeReflectionLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  adequacy_prop_from_star_counterexample (Γ := Γ) (φ := φ) hΓ hφ

theorem core_completeness_prop_from_canonical_prime_rel_via_star_seed_lift
    {σ : Type}
    [HasCanonicalPrimeRelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RM.Entails Γ φ → NDRMSyntax.DerivesCore Γ φ := by
  letI : HasCanonicalStarProp σ := canonicalStarPropOfPrimeRel (σ := σ)
  letI : CanonicalPair.HasPrimeTransferLift σ :=
    canonicalPair_hasPrimeTransferLift_of_prime_rel (σ := σ)
  exact core_completeness_prop_from_star_transfer_lift (Γ := Γ) (φ := φ) hΓ hφ

theorem completeness_prop_from_canonical_prime_rel_via_star_seed_lift
    {σ : Type}
    [HasCanonicalPrimeRelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RM.Entails Γ φ → NDRMSyntax.Derives Γ φ := by
  letI : HasCanonicalStarProp σ := canonicalStarPropOfPrimeRel (σ := σ)
  letI : CanonicalPair.HasPrimeTransferLift σ :=
    canonicalPair_hasPrimeTransferLift_of_prime_rel (σ := σ)
  exact completeness_prop_from_star_transfer_lift (Γ := Γ) (φ := φ) hΓ hφ

theorem adequacy_prop_from_star_seed_lift
    {σ : Type}
    [HasCanonicalStarProp σ]
    [CanonicalPair.HasPrimeLift σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  adequacy_prop_from_star_counterexample (Γ := Γ) (φ := φ) hΓ hφ

theorem adequacy_prop_from_canonical_prime_rel_via_star_seed_lift
    {σ : Type}
    [HasCanonicalPrimeRelProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ := by
  letI : HasCanonicalStarProp σ := canonicalStarPropOfPrimeRel (σ := σ)
  letI : CanonicalPair.HasPrimeTransferLift σ :=
    canonicalPair_hasPrimeTransferLift_of_prime_rel (σ := σ)
  exact adequacy_prop_from_star_transfer_lift (Γ := Γ) (φ := φ) hΓ hφ

theorem adequacy_prop_from_star_seed_lift_of_counterexample
    {σ : Type}
    [HasCanonicalStarProp σ]
    [HasCanonicalImpCounterexampleProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ := by
  letI : CanonicalPair.HasPrimeLift σ :=
    CanonicalPair.hasPrimeLift_of_counterexample (σ := σ)
  exact adequacy_prop_from_star_seed_lift (Γ := Γ) (φ := φ) hΓ hφ

theorem core_completeness_prop_from_star_exists_counterexample
    {σ : Type}
    [HasCanonicalStarProp σ]
    [HasCanonicalImpCounterexampleProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RM.Entails Γ φ → NDRMSyntax.DerivesCore Γ φ :=
  core_completeness_prop_from_star_counterexample (Γ := Γ) (φ := φ) hΓ hφ

theorem completeness_prop_from_star_exists_counterexample
    {σ : Type}
    [HasCanonicalStarProp σ]
    [HasCanonicalImpCounterexampleProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    RM.Entails Γ φ → NDRMSyntax.Derives Γ φ :=
  completeness_prop_from_star_counterexample (Γ := Γ) (φ := φ) hΓ hφ

theorem adequacy_prop_from_star_exists_counterexample
    {σ : Type}
    [HasCanonicalStarProp σ]
    [HasCanonicalImpCounterexampleProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    NDRMSyntax.Derives Γ φ ↔ RM.Entails Γ φ :=
  adequacy_prop_from_star_counterexample (Γ := Γ) (φ := φ) hΓ hφ

end RM
end Noneism
end HeytingLean
