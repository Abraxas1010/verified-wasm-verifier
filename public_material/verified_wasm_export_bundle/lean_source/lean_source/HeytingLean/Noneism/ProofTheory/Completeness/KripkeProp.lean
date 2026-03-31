import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Zorn
import HeytingLean.Noneism.ProofTheory.ND
import HeytingLean.Noneism.Semantics.KripkeProp

/-!
# Noneism.ProofTheory.Completeness.KripkeProp

Completeness of the **propositional** natural-deduction system `DerivesProp` with respect to the
propositional Kripke semantics in `Noneism.Semantics.KripkeProp`.

Main theorem (propositional fragment):

`KripkeProp.Entails Γ φ`  ⇒  `DerivesProp Γ φ`.

We treat `pred` and `eExists` as atoms, matching both the proof system and the Kripke semantics.

The proof is classical and uses Zorn's lemma (Lindenbaum construction) to build prime theories,
which serve as Kripke worlds.
-/

namespace HeytingLean
namespace Noneism

open scoped Classical

open Formula

namespace KripkeProp
namespace Completeness

variable {σ : Type}

/-! ## Derivability from sets (finite contexts) -/

/-- `Derivable T φ` means: there is a finite context (a list) of assumptions from `T` that proves
`φ` in the finitary proof system `DerivesProp`.

This bridges potentially-infinite theories `T : Set (Formula σ)` and the list-based ND system.
-/
def Derivable (T : Set (Formula σ)) (φ : Formula σ) : Prop :=
  ∃ Γ : List (Formula σ), (∀ ψ ∈ Γ, ψ ∈ T) ∧ DerivesProp (σ := σ) Γ φ

/-- A set is consistent if it does not (finitely) derive `⊥`. -/
def Consistent (T : Set (Formula σ)) : Prop :=
  ¬ Derivable (σ := σ) T (.bot : Formula σ)

lemma derivable_of_mem {T : Set (Formula σ)} {φ : Formula σ} (hφ : φ ∈ T) :
    Derivable (σ := σ) T φ := by
  refine ⟨[φ], ?_, ?_⟩
  · intro ψ hψ
    simp at hψ
    subst hψ
    exact hφ
  · exact DerivesProp.hyp (by simp)

lemma derivable_of_derivesProp {T : Set (Formula σ)} {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, ψ ∈ T) (h : DerivesProp (σ := σ) Γ φ) :
    Derivable (σ := σ) T φ :=
  ⟨Γ, hΓ, h⟩

lemma Derivable.mono {T U : Set (Formula σ)} {φ : Formula σ} (hTU : T ⊆ U) :
    Derivable (σ := σ) T φ → Derivable (σ := σ) U φ := by
  rintro ⟨Γ, hΓ, hDer⟩
  refine ⟨Γ, ?_, hDer⟩
  intro ψ hψ
  exact hTU (hΓ ψ hψ)

/-! ## Eliminating an inserted assumption -/

/-!
If `φ` is derivable from `T`, then any derivation from `insert φ T` can be turned into a derivation
from `T` by discharging `φ` as an implication and applying modus ponens.\n
\n
This is the key lemma used to show that adding a *derivable* formula does not create new
derivations of `⊥` (consistency) or of a forbidden formula `χ`.\n
-/
lemma derivable_of_insert {T : Set (Formula σ)} {φ χ : Formula σ}
    (hφ : Derivable (σ := σ) T φ) :
    Derivable (σ := σ) (Set.insert φ T) χ → Derivable (σ := σ) T χ := by
  rintro ⟨Γ, hΓ, hDerχ⟩
  classical
  -- Remove occurrences of `φ` from the context (they can be supplied by `hφ`).
  let Δ : List (Formula σ) := Γ.filter (fun t => decide (t ≠ φ))
  have hΔT : ∀ t ∈ Δ, t ∈ T := by
    intro t ht
    have htΓ : t ∈ Γ := (List.mem_filter.1 ht).1
    have htIns : t ∈ Set.insert φ T := hΓ t htΓ
    rcases htIns with htEq | htT
    · have htne : t ≠ φ := (decide_eq_true_iff).1 (List.mem_filter.1 ht).2
      exact False.elim (htne htEq)
    · exact htT
  have hsub : Γ ⊆ (φ :: Δ) := by
    intro t ht
    by_cases htφ : t = φ
    · subst htφ
      simp
    · have : t ∈ Δ := by
        refine List.mem_filter.2 ?_
        refine ⟨ht, ?_⟩
        simpa using (decide_eq_true_iff).2 htφ
      exact List.mem_cons_of_mem _ this
  have hDerχ' : DerivesProp (σ := σ) (φ :: Δ) χ :=
    DerivesProp.weaken (σ := σ) hDerχ (Δ := φ :: Δ) hsub
  -- Discharge `φ` to get `φ → χ` from `Δ`.
  have hImp : DerivesProp (σ := σ) Δ (.imp φ χ) := DerivesProp.impI hDerχ'
  rcases hφ with ⟨Γφ, hΓφ, hDerφ⟩
  have hImp' : DerivesProp (σ := σ) (Δ ++ Γφ) (.imp φ χ) :=
    DerivesProp.weaken (σ := σ) hImp (Δ := Δ ++ Γφ) (by
      intro θ hθ
      exact List.mem_append_left _ hθ)
  have hDerφ' : DerivesProp (σ := σ) (Δ ++ Γφ) φ :=
    DerivesProp.weaken (σ := σ) hDerφ (Δ := Δ ++ Γφ) (by
      intro θ hθ
      exact List.mem_append_right _ hθ)
  have hDerχ'' : DerivesProp (σ := σ) (Δ ++ Γφ) χ := DerivesProp.impE hImp' hDerφ'
  refine ⟨Δ ++ Γφ, ?_, hDerχ''⟩
  intro θ hθ
  have : θ ∈ Δ ∨ θ ∈ Γφ := by
    simpa [List.mem_append] using hθ
  cases this with
  | inl hθΔ => exact hΔT θ hθΔ
  | inr hθΓ => exact hΓφ θ hθΓ

/-! ## Prime theories (Kripke worlds) -/

/-- A prime theory (intuitionistic): consistent, deductively closed, and has the disjunction
property. -/
structure PrimeTheory (σ : Type) where
  carrier : Set (Formula σ)
  consistent : Consistent (σ := σ) carrier
  closed : ∀ φ : Formula σ, Derivable (σ := σ) carrier φ → φ ∈ carrier
  prime : ∀ φ ψ : Formula σ, (.or φ ψ) ∈ carrier → φ ∈ carrier ∨ ψ ∈ carrier

/-! ## Lindenbaum construction via Zorn -/

namespace Lindenbaum

/-- Zorn family: consistent extensions of `S` that do not derive `χ`. -/
def Family (S : Set (Formula σ)) (χ : Formula σ) : Set (Set (Formula σ)) :=
  {T | Consistent (σ := σ) T ∧ S ⊆ T ∧ ¬ Derivable (σ := σ) T χ}

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
  · -- consistency of the union
    intro hbot
    rcases hbot with ⟨Γ, hΓ, hDerBot⟩
    let fs : Finset (Formula σ) := Γ.toFinset
    have hfsfin : (fs : Set (Formula σ)).Finite := fs.finite_toSet
    have hfsSub : (fs : Set (Formula σ)) ⊆ Set.sUnion c := by
      intro φ hφ
      -- `φ ∈ Γ`, hence in `sUnion c`
      have : φ ∈ Γ := by
        exact List.mem_toFinset.1 hφ
      exact hΓ φ this
    have hdir : DirectedOn (· ⊆ ·) c := chain_directedOn (hc := hc)
    rcases
        DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion
          (α := Formula σ) (c := c) hcne hdir (s := (fs : Set (Formula σ))) hfsfin hfsSub with
      ⟨t, htC, hfst⟩
    have hΓt : ∀ ψ ∈ Γ, ψ ∈ t := by
      intro ψ hψ
      have : ψ ∈ (fs : Set (Formula σ)) := by
        exact List.mem_toFinset.2 hψ
      exact hfst this
    have htCons : Consistent (σ := σ) t := (hcF htC).1
    exact htCons (derivable_of_derivesProp (σ := σ) (T := t) (Γ := Γ) (φ := .bot)
      (by intro ψ hψ; exact hΓt ψ hψ) hDerBot)
  · -- base inclusion
    intro φ hφ
    rcases hcne with ⟨t, htC⟩
    have hSt : S ⊆ t := (hcF htC).2.1
    exact Set.subset_sUnion_of_mem htC (hSt hφ)
  · -- does not derive `χ`
    intro hχ
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
    exact htNo (derivable_of_derivesProp (σ := σ) (T := t) (Γ := Γ) (φ := χ)
      (by intro ψ hψ; exact hΓt ψ hψ) hDerχ)

/-- Existence of a maximal element of `Family S χ` extending `S`. -/
lemma exists_maximal (S : Set (Formula σ)) (χ : Formula σ)
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

/-- If `M` is maximal in `Family S χ`, then any derivable formula already lies in `M`. -/
lemma closed_of_maximal {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)}
    (hMF : M ∈ Family (σ := σ) S χ)
    (hMax : Maximal (· ∈ Family (σ := σ) S χ) M) :
    ∀ φ : Formula σ, Derivable (σ := σ) M φ → φ ∈ M := by
  classical
  intro φ hDer
  by_contra hmem
  have hSsub : S ⊆ M := hMF.2.1
  have hCons : Consistent (σ := σ) M := hMF.1
  have hNoχ : ¬ Derivable (σ := σ) M χ := hMF.2.2

  have hConsIns : Consistent (σ := σ) (Set.insert φ M) := by
    intro hbot
    have : Derivable (σ := σ) M (.bot : Formula σ) :=
      derivable_of_insert (σ := σ) (T := M) (φ := φ) (χ := .bot) hDer hbot
    exact hCons this

  have hNoχIns : ¬ Derivable (σ := σ) (Set.insert φ M) χ := by
    intro hχ
    have : Derivable (σ := σ) M χ :=
      derivable_of_insert (σ := σ) (T := M) (φ := φ) (χ := χ) hDer hχ
    exact hNoχ this

  have hFamIns : Set.insert φ M ∈ Family (σ := σ) S χ := by
    refine ⟨hConsIns, ?_, hNoχIns⟩
    intro θ hθ
    exact Or.inr (hSsub hθ)

  have hsub : M ⊆ Set.insert φ M := by
    intro θ hθ
    exact Or.inr hθ

  have hEq : Set.insert φ M = M := (hMax.eq_of_subset hFamIns hsub).symm
  have : φ ∈ M := by
    have : φ ∈ Set.insert φ M := Or.inl rfl
    simpa [hEq] using this
  exact hmem this

/-- Maximal sets in `Family S χ` satisfy the disjunction property. -/
lemma prime_of_maximal {S : Set (Formula σ)} {χ : Formula σ} {M : Set (Formula σ)}
    (hMF : M ∈ Family (σ := σ) S χ)
    (hMax : Maximal (· ∈ Family (σ := σ) S χ) M)
    (hClosed : ∀ φ : Formula σ, Derivable (σ := σ) M φ → φ ∈ M) :
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

  -- By maximality: if we can't add a disjunct while staying in the family,
  -- then we can derive `χ` under that disjunct.
  have hDerIns (th : Formula σ) (hth : th ∉ M) :
      Derivable (σ := σ) (Set.insert th M) χ := by
    by_contra hno
    have hConsIns : Consistent (σ := σ) (Set.insert th M) := by
      intro hbot
      rcases hbot with ⟨Γ, hΓ, hDerBot⟩
      -- from `⊥` we can derive `χ`, contradicting `hno`.
      have hDerχ : DerivesProp (σ := σ) Γ χ := DerivesProp.botE hDerBot
      exact hno ⟨Γ, hΓ, hDerχ⟩
    have hSsub : S ⊆ M := hMF.2.1
    have hFamIns : Set.insert th M ∈ Family (σ := σ) S χ := by
      refine ⟨hConsIns, ?_, hno⟩
      intro x hx
      exact Or.inr (hSsub hx)
    have hsub : M ⊆ Set.insert th M := by
      intro x hx
      exact Or.inr hx
    have hEq : Set.insert th M = M := (hMax.eq_of_subset hFamIns hsub).symm
    exact hth (by
      have : th ∈ Set.insert th M := Or.inl rfl
      simpa [hEq] using this)

  have hImp_from (th : Formula σ) (hth : th ∉ M) :
      Derivable (σ := σ) M (.imp th χ) := by
    rcases hDerIns th hth with ⟨Γ, hΓ, hDerχ⟩
    classical
    let Δ : List (Formula σ) := Γ.filter (fun t => decide (t ≠ th))
    have hΔM : ∀ t ∈ Δ, t ∈ M := by
      intro t ht
      have htΓ : t ∈ Γ := (List.mem_filter.1 ht).1
      have htIns : t ∈ Set.insert th M := hΓ t htΓ
      rcases htIns with htEq | htM
      · have htne : t ≠ th := (decide_eq_true_iff).1 (List.mem_filter.1 ht).2
        exact False.elim (htne htEq)
      · exact htM
    have hsub : Γ ⊆ (th :: Δ) := by
      intro t ht
      by_cases htth : t = th
      · subst htth
        simp
      · have : t ∈ Δ := by
          refine List.mem_filter.2 ?_
          refine ⟨ht, ?_⟩
          simpa using (decide_eq_true_iff).2 htth
        exact List.mem_cons_of_mem _ this
    have hDerχ' : DerivesProp (σ := σ) (th :: Δ) χ :=
      DerivesProp.weaken (σ := σ) hDerχ (Δ := th :: Δ) hsub
    have hImp : DerivesProp (σ := σ) Δ (.imp th χ) := DerivesProp.impI hDerχ'
    exact derivable_of_derivesProp (σ := σ) (T := M) (Γ := Δ) (φ := .imp th χ) hΔM hImp

  have hImpφ : Derivable (σ := σ) M (.imp φ χ) := hImp_from φ hφ
  have hImpψ : Derivable (σ := σ) M (.imp ψ χ) := hImp_from ψ hψ

  have himpφ : (.imp φ χ) ∈ M := hClosed _ hImpφ
  have himpψ : (.imp ψ χ) ∈ M := hClosed _ hImpψ

  -- From `φ ∨ ψ` and both implications, derive `χ`.
  have hχM : Derivable (σ := σ) M χ := by
    refine ⟨[.or φ ψ, .imp φ χ, .imp ψ χ], ?_, ?_⟩
    · intro t ht
      simp at ht
      rcases ht with rfl | rfl | rfl
      · exact hor
      · exact himpφ
      · exact himpψ
    · have hOr : DerivesProp (σ := σ) [.or φ ψ, .imp φ χ, .imp ψ χ] (.or φ ψ) :=
        DerivesProp.hyp (by simp)
      have hLeft : DerivesProp (σ := σ) (φ :: [.or φ ψ, .imp φ χ, .imp ψ χ]) χ := by
        have hImp : DerivesProp (σ := σ) (φ :: [.or φ ψ, .imp φ χ, .imp ψ χ]) (.imp φ χ) :=
          DerivesProp.hyp (by simp)
        have hφ' : DerivesProp (σ := σ) (φ :: [.or φ ψ, .imp φ χ, .imp ψ χ]) φ :=
          DerivesProp.hyp (by simp)
        exact DerivesProp.impE hImp hφ'
      have hRight : DerivesProp (σ := σ) (ψ :: [.or φ ψ, .imp φ χ, .imp ψ χ]) χ := by
        have hImp : DerivesProp (σ := σ) (ψ :: [.or φ ψ, .imp φ χ, .imp ψ χ]) (.imp ψ χ) :=
          DerivesProp.hyp (by simp)
        have hψ' : DerivesProp (σ := σ) (ψ :: [.or φ ψ, .imp φ χ, .imp ψ χ]) ψ :=
          DerivesProp.hyp (by simp)
        exact DerivesProp.impE hImp hψ'
      exact DerivesProp.orE hOr hLeft hRight

  exact (hMF.2.2) hχM

/-- Build a prime theory extending `S` and avoiding derivability (hence membership) of `χ`. -/
theorem exists_primeTheory_avoid (S : Set (Formula σ)) (χ : Formula σ)
    (hS : Consistent (σ := σ) S) (hχ : ¬ Derivable (σ := σ) S χ) :
    ∃ W : PrimeTheory σ, S ⊆ W.carrier ∧ χ ∉ W.carrier := by
  classical
  rcases exists_maximal (σ := σ) S χ hS hχ with ⟨M, hSM, hMax⟩
  have hMF : M ∈ Family (σ := σ) S χ := hMax.prop
  have hClosed : ∀ φ : Formula σ, Derivable (σ := σ) M φ → φ ∈ M :=
    closed_of_maximal (σ := σ) (S := S) (χ := χ) (M := M) hMF hMax
  have hPrime : ∀ φ ψ : Formula σ, (.or φ ψ) ∈ M → φ ∈ M ∨ ψ ∈ M :=
    prime_of_maximal (σ := σ) (S := S) (χ := χ) (M := M) hMF hMax hClosed
  have hNotMem : χ ∉ M := by
    intro hMem
    exact hMF.2.2 (derivable_of_mem (σ := σ) (T := M) hMem)
  refine ⟨⟨M, hMF.1, hClosed, hPrime⟩, hSM, hNotMem⟩

end Lindenbaum

/-! ## Canonical Kripke model on prime theories -/

namespace Canonical

open Lindenbaum

abbrev W : Type := PrimeTheory σ

-- Canonical Kripke frame order: extension by inclusion of theories.
instance : LE (PrimeTheory σ) := ⟨fun w v => w.carrier ⊆ v.carrier⟩

instance : Preorder (PrimeTheory σ) where
  le := (· ≤ ·)
  le_refl _ := by
    exact subset_rfl
  le_trans _ _ _ hab hbc := by
    exact Set.Subset.trans hab hbc

/-- Canonical Kripke model: atoms are forced iff they are members of the prime theory. -/
def model : KripkeProp.Model (PrimeTheory σ) σ where
  valPred w p args := (.pred p args : Formula σ) ∈ w.carrier
  monoPred := by
    intro w v hwv p args h
    exact hwv h
  valEx w t := (.eExists t : Formula σ) ∈ w.carrier
  monoEx := by
    intro w v hwv t h
    exact hwv h

/-- Truth lemma: forcing is equivalent to membership, for propositional formulas. -/
theorem forces_iff_mem (w : PrimeTheory σ) :
    ∀ {φ : Formula σ}, IsProp (σ := σ) φ →
      (Forces model w φ ↔ φ ∈ w.carrier) := by
  intro φ hprop
  induction hprop generalizing w with
  | top =>
      constructor
      · intro _
        have hDer : Derivable (σ := σ) w.carrier (.top : Formula σ) :=
          ⟨[], by simp, DerivesProp.topI⟩
        exact w.closed _ hDer
      · intro _; trivial
  | bot =>
      constructor
      · intro h; cases (show False from h)
      · intro hmem
        exact (w.consistent (derivable_of_mem (σ := σ) (T := w.carrier) hmem)).elim
  | pred p args =>
      simp [model, KripkeProp.Forces]
  | eExists t =>
      simp [model, KripkeProp.Forces]
  | and hφ hψ ihφ ihψ =>
      rename_i φ ψ
      constructor
      · intro hForce
        have hmemφ : φ ∈ w.carrier := (ihφ (w := w)).1 hForce.1
        have hmemψ : ψ ∈ w.carrier := (ihψ (w := w)).1 hForce.2
        have hDer : Derivable (σ := σ) w.carrier (.and φ ψ) := by
          refine ⟨[φ, ψ], ?_, ?_⟩
          · intro t ht
            simp at ht
            rcases ht with rfl | rfl
            · exact hmemφ
            · exact hmemψ
          ·
            have hφ' : DerivesProp (σ := σ) [φ, ψ] φ := DerivesProp.hyp (by simp)
            have hψ' : DerivesProp (σ := σ) [φ, ψ] ψ := DerivesProp.hyp (by simp)
            exact DerivesProp.andI hφ' hψ'
        exact w.closed _ hDer
      · intro hmemAnd
        have hφmem : φ ∈ w.carrier := by
          rcases derivable_of_mem (σ := σ) (T := w.carrier) hmemAnd with ⟨Γ, hΓ, hDer⟩
          exact w.closed _ ⟨Γ, hΓ, DerivesProp.andEL hDer⟩
        have hψmem : ψ ∈ w.carrier := by
          rcases derivable_of_mem (σ := σ) (T := w.carrier) hmemAnd with ⟨Γ, hΓ, hDer⟩
          exact w.closed _ ⟨Γ, hΓ, DerivesProp.andER hDer⟩
        exact And.intro ((ihφ (w := w)).2 hφmem) ((ihψ (w := w)).2 hψmem)
  | or hφ hψ ihφ ihψ =>
      rename_i φ ψ
      constructor
      · intro hForce
        cases hForce with
        | inl hφForce =>
            have hmemφ : φ ∈ w.carrier := (ihφ (w := w)).1 hφForce
            have hDer : Derivable (σ := σ) w.carrier (.or φ ψ) := by
              refine ⟨[φ], ?_, ?_⟩
              · intro t ht
                simp at ht
                subst ht
                exact hmemφ
              ·
                have hφ' : DerivesProp (σ := σ) [φ] φ := DerivesProp.hyp (by simp)
                exact DerivesProp.orIL hφ'
            exact w.closed _ hDer
        | inr hψForce =>
            have hmemψ : ψ ∈ w.carrier := (ihψ (w := w)).1 hψForce
            have hDer : Derivable (σ := σ) w.carrier (.or φ ψ) := by
              refine ⟨[ψ], ?_, ?_⟩
              · intro t ht
                simp at ht
                subst ht
                exact hmemψ
              ·
                have hψ' : DerivesProp (σ := σ) [ψ] ψ := DerivesProp.hyp (by simp)
                exact DerivesProp.orIR hψ'
            exact w.closed _ hDer
      · intro hmemOr
        have hmem : φ ∈ w.carrier ∨ ψ ∈ w.carrier := w.prime _ _ hmemOr
        cases hmem with
        | inl hmemφ => exact Or.inl ((ihφ (w := w)).2 hmemφ)
        | inr hmemψ => exact Or.inr ((ihψ (w := w)).2 hmemψ)
  | not hφ ihφ =>
      rename_i φ
      constructor
      · intro hForce
        by_contra hmemNot
        -- If `¬φ ∉ w`, then `insert φ w` is consistent; extend to a prime theory forcing `φ`.
        have hCons : Consistent (σ := σ) (Set.insert φ w.carrier) := by
          intro hbot
          rcases hbot with ⟨Γ, hΓ, hDerBot⟩
          classical
          let Δ : List (Formula σ) := Γ.filter (fun t => decide (t ≠ φ))
          have hΔw : ∀ t ∈ Δ, t ∈ w.carrier := by
            intro t ht
            have htΓ : t ∈ Γ := (List.mem_filter.1 ht).1
            have htIns : t ∈ Set.insert φ w.carrier := hΓ t htΓ
            rcases htIns with htEq | htW
            · have htne : t ≠ φ := (decide_eq_true_iff).1 (List.mem_filter.1 ht).2
              exact False.elim (htne htEq)
            · exact htW
          have hsub : Γ ⊆ (φ :: Δ) := by
            intro t ht
            by_cases htφ : t = φ
            · subst htφ; simp
            ·
              have : t ∈ Δ := by
                refine List.mem_filter.2 ⟨ht, ?_⟩
                simpa using (decide_eq_true_iff).2 htφ
              exact List.mem_cons_of_mem _ this
          have hDerBot' :
              DerivesProp (σ := σ) (φ :: Δ) (.bot : Formula σ) :=
            DerivesProp.weaken (σ := σ) hDerBot (Δ := φ :: Δ) hsub
          have hNot : DerivesProp (σ := σ) Δ (.not φ) :=
            DerivesProp.notI hDerBot'
          have hNotD : Derivable (σ := σ) w.carrier (.not φ) :=
            derivable_of_derivesProp (σ := σ) (T := w.carrier) (Γ := Δ) (φ := .not φ) hΔw hNot
          exact hmemNot (w.closed _ hNotD)
        have hNotDerBot :
            ¬ Derivable (σ := σ) (Set.insert φ w.carrier) (.bot : Formula σ) := hCons
        rcases
            Lindenbaum.exists_primeTheory_avoid (σ := σ) (S := Set.insert φ w.carrier)
              (χ := (.bot : Formula σ)) hCons hNotDerBot with
          ⟨v, hwv, _⟩
        have hv_ge : w ≤ v := by
          intro θ hθ
          exact hwv (Or.inr hθ)
        have hvφmem : φ ∈ v.carrier := hwv (Or.inl rfl)
        have hvφ : Forces model v φ := (ihφ (w := v)).2 hvφmem
        exact hForce v hv_ge hvφ
      · intro hmemNot v hwv hvφ
        have hNotv : (.not φ : Formula σ) ∈ v.carrier := hwv hmemNot
        have hφmem : φ ∈ v.carrier := (ihφ (w := v)).1 hvφ
        have hBotD : Derivable (σ := σ) v.carrier (.bot : Formula σ) := by
          refine ⟨[.not φ, φ], ?_, ?_⟩
          · intro t ht
            simp at ht
            rcases ht with rfl | rfl
            · exact hNotv
            · exact hφmem
          ·
            have h1 : DerivesProp (σ := σ) [.not φ, φ] (.not φ) := DerivesProp.hyp (by simp)
            have h2 : DerivesProp (σ := σ) [.not φ, φ] φ := DerivesProp.hyp (by simp)
            exact DerivesProp.notE h1 h2
        exact (v.consistent hBotD)
  | imp hφ hψ ihφ ihψ =>
      rename_i φ ψ
      constructor
      · intro hForce
        by_contra hmemImp
        -- Build an extension world that forces `φ` but not `ψ`.
        have hCons : Consistent (σ := σ) (Set.insert φ w.carrier) := by
          intro hbot
          rcases hbot with ⟨Γ, hΓ, hDerBot⟩
          classical
          let Δ : List (Formula σ) := Γ.filter (fun t => decide (t ≠ φ))
          have hΔw : ∀ t ∈ Δ, t ∈ w.carrier := by
            intro t ht
            have htΓ : t ∈ Γ := (List.mem_filter.1 ht).1
            have htIns : t ∈ Set.insert φ w.carrier := hΓ t htΓ
            rcases htIns with htEq | htW
            · have htne : t ≠ φ := (decide_eq_true_iff).1 (List.mem_filter.1 ht).2
              exact False.elim (htne htEq)
            · exact htW
          have hsub : Γ ⊆ (φ :: Δ) := by
            intro t ht
            by_cases htφ : t = φ
            · subst htφ; simp
            ·
              have : t ∈ Δ := by
                refine List.mem_filter.2 ⟨ht, ?_⟩
                simpa using (decide_eq_true_iff).2 htφ
              exact List.mem_cons_of_mem _ this
          have hDerBot' :
              DerivesProp (σ := σ) (φ :: Δ) (.bot : Formula σ) :=
            DerivesProp.weaken (σ := σ) hDerBot (Δ := φ :: Δ) hsub
          have hNot : DerivesProp (σ := σ) Δ (.not φ) :=
            DerivesProp.notI hDerBot'
          have hNotD : Derivable (σ := σ) w.carrier (.not φ) :=
            derivable_of_derivesProp (σ := σ) (T := w.carrier) (Γ := Δ) (φ := .not φ) hΔw hNot
          have hNotMem : (.not φ) ∈ w.carrier := w.closed _ hNotD
          -- From `¬φ`, derive `φ → ψ`.
          have hImpD : Derivable (σ := σ) w.carrier (.imp φ ψ) := by
            refine ⟨[.not φ], ?_, ?_⟩
            · intro t ht
              simp at ht
              subst ht
              exact hNotMem
            ·
              have hNot' : DerivesProp (σ := σ) [.not φ] (.not φ) := DerivesProp.hyp (by simp)
              have hBot : DerivesProp (σ := σ) (φ :: [.not φ]) (.bot : Formula σ) := by
                have hNot'' : DerivesProp (σ := σ) (φ :: [.not φ]) (.not φ) :=
                  DerivesProp.weaken (σ := σ) hNot' (Δ := φ :: [.not φ]) (by
                    intro θ hθ
                    exact List.mem_cons_of_mem _ hθ)
                have hφ' : DerivesProp (σ := σ) (φ :: [.not φ]) φ := DerivesProp.hyp (by simp)
                exact DerivesProp.notE hNot'' hφ'
              have hψ' : DerivesProp (σ := σ) (φ :: [.not φ]) ψ := DerivesProp.botE hBot
              exact DerivesProp.impI hψ'
          exact hmemImp (w.closed _ hImpD)
        have hNotDer : ¬ Derivable (σ := σ) (Set.insert φ w.carrier) ψ := by
          intro hDer
          rcases hDer with ⟨Γ, hΓ, hDerψ⟩
          classical
          let Δ : List (Formula σ) := Γ.filter (fun t => decide (t ≠ φ))
          have hΔw : ∀ t ∈ Δ, t ∈ w.carrier := by
            intro t ht
            have htΓ : t ∈ Γ := (List.mem_filter.1 ht).1
            have htIns : t ∈ Set.insert φ w.carrier := hΓ t htΓ
            rcases htIns with htEq | htW
            · have htne : t ≠ φ := (decide_eq_true_iff).1 (List.mem_filter.1 ht).2
              exact False.elim (htne htEq)
            · exact htW
          have hsub : Γ ⊆ (φ :: Δ) := by
            intro t ht
            by_cases htφ : t = φ
            · subst htφ; simp
            ·
              have : t ∈ Δ := by
                refine List.mem_filter.2 ⟨ht, ?_⟩
                simpa using (decide_eq_true_iff).2 htφ
              exact List.mem_cons_of_mem _ this
          have hDerψ' : DerivesProp (σ := σ) (φ :: Δ) ψ :=
            DerivesProp.weaken (σ := σ) hDerψ (Δ := φ :: Δ) hsub
          have hImp : DerivesProp (σ := σ) Δ (.imp φ ψ) := DerivesProp.impI hDerψ'
          have hImpD : Derivable (σ := σ) w.carrier (.imp φ ψ) :=
            derivable_of_derivesProp (σ := σ) (T := w.carrier) (Γ := Δ) (φ := .imp φ ψ) hΔw hImp
          exact hmemImp (w.closed _ hImpD)
        rcases
            Lindenbaum.exists_primeTheory_avoid (σ := σ) (S := Set.insert φ w.carrier)
              (χ := ψ) hCons hNotDer with
          ⟨v, hwv, hψNotMem⟩
        have hv_ge : w ≤ v := by
          intro θ hθ
          exact hwv (Or.inr hθ)
        have hvφmem : φ ∈ v.carrier := hwv (Or.inl rfl)
        have hvφ : Forces model v φ := (ihφ (w := v)).2 hvφmem
        have hvψFalse : ¬ Forces model v ψ := by
          intro hvψ
          have : ψ ∈ v.carrier := (ihψ (w := v)).1 hvψ
          exact hψNotMem this
        exact hvψFalse (hForce v hv_ge hvφ)
      · intro hmemImp v hwv hvφ
        have hImpv : (.imp φ ψ : Formula σ) ∈ v.carrier := hwv hmemImp
        have hφmem : φ ∈ v.carrier := (ihφ (w := v)).1 hvφ
        have hψD : Derivable (σ := σ) v.carrier ψ := by
          refine ⟨[.imp φ ψ, φ], ?_, ?_⟩
          · intro t ht
            simp at ht
            rcases ht with rfl | rfl
            · exact hImpv
            · exact hφmem
          ·
            have h1 : DerivesProp (σ := σ) [.imp φ ψ, φ] (.imp φ ψ) := DerivesProp.hyp (by simp)
            have h2 : DerivesProp (σ := σ) [.imp φ ψ, φ] φ := DerivesProp.hyp (by simp)
            exact DerivesProp.impE h1 h2
        have hψmem : ψ ∈ v.carrier := v.closed _ hψD
        exact (ihψ (w := v)).2 hψmem

end Canonical

/-! ## Completeness theorem -/

open Canonical Lindenbaum

theorem completeness {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, IsProp (σ := σ) ψ)
    (hφ : IsProp (σ := σ) φ) :
    Entails (σ := σ) Γ φ → DerivesProp (σ := σ) Γ φ := by
  intro hEnt
  -- contrapositive: if not derivable, build a canonical countermodel.
  by_contra hDer
  classical
  let S : Set (Formula σ) := fun ψ => ψ ∈ Γ
  have hSCons : Consistent (σ := σ) S := by
    intro hbot
    rcases hbot with ⟨Δ, hΔ, hDerBot⟩
    have hDerBotΓ : DerivesProp (σ := σ) Γ (.bot : Formula σ) :=
      DerivesProp.weaken (σ := σ) hDerBot (Δ := Γ) (by
        intro ψ hψ
        exact hΔ ψ hψ)
    have : DerivesProp (σ := σ) Γ φ := DerivesProp.botE hDerBotΓ
    exact hDer this
  have hNotDer : ¬ Derivable (σ := σ) S φ := by
    intro hD
    rcases hD with ⟨Δ, hΔ, hDerφ⟩
    have hDerφΓ : DerivesProp (σ := σ) Γ φ :=
      DerivesProp.weaken (σ := σ) hDerφ (Δ := Γ) (by
        intro ψ hψ
        exact hΔ ψ hψ)
    exact hDer hDerφΓ

  rcases Lindenbaum.exists_primeTheory_avoid (σ := σ) (S := S) (χ := φ) hSCons hNotDer with
    ⟨w, hSw, hNotMem⟩

  have hForcesΓ : ∀ ψ ∈ Γ, Forces (Canonical.model (σ := σ)) w ψ := by
    intro ψ hψ
    have hmem : ψ ∈ w.carrier := hSw hψ
    have hprop : IsProp (σ := σ) ψ := hΓ ψ hψ
    exact (Canonical.forces_iff_mem (σ := σ) (w := w) (φ := ψ) hprop).2 hmem

  have hForcesφ : Forces (Canonical.model (σ := σ)) w φ :=
    hEnt (W := Canonical.W (σ := σ)) (M := Canonical.model (σ := σ)) (w := w) hForcesΓ

  have : φ ∈ w.carrier := (Canonical.forces_iff_mem (σ := σ) (w := w) (φ := φ) hφ).1 hForcesφ
  exact hNotMem this

end Completeness
end KripkeProp

end Noneism
end HeytingLean
