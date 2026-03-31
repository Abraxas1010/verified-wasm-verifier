import HeytingLean.Noneism.Syntax
import HeytingLean.Noneism.Syntax.Subst

/-!
# Noneism.ProofTheory.ND

Natural-deduction style proof theory for the Noneism object language.

Why this exists:
- Prior to this module, Noneism had multiple semantics (Sylvan/LP/Routley–Meyer/ModalPriest) but no
  *internal* derivability relation. This made the ontology layer "minimal" (semantic-only).
- Adding a proof theory lets us state and prove **soundness** theorems (and later completeness),
  which is the step that makes the foundational story "maximally implemented" in Lean.

Scope:
- Connectives: ⊤, ⊥, ¬, ∧, ∨, →
- Atomic formulas: `pred` and `eExists` are treated as atoms here (no special rules yet).
- Quantifiers (`sigma` / `pi`) are handled in the `Derives` system (first-order-ish rules)
  using capture-avoiding substitution from `Noneism.Syntax.Subst`.

Future work:
- Completeness for the first-order fragment.
  - Design docs / blockers: `WIP/noneism_fo_henkin_completeness_plan_2026-02-09.md` and
    `WIP/noneism_internal_fo_completeness_blockers_2026-02-06.md`.
- Add alternative proof systems (e.g. sequent calculus) and prove equivalence.
-/

namespace HeytingLean
namespace Noneism

open Formula

namespace ND

open Syntax

def fvContext {σ : Type} (Γ : List (Formula σ)) : Finset Var :=
  Γ.foldr (fun φ acc => Syntax.fvFormula φ ∪ acc) ∅

@[simp] theorem fvContext_nil {σ : Type} :
    fvContext (σ := σ) ([] : List (Formula σ)) = ∅ := rfl

@[simp] theorem fvContext_cons {σ : Type} (φ : Formula σ) (Γ : List (Formula σ)) :
    fvContext (σ := σ) (φ :: Γ) = Syntax.fvFormula φ ∪ fvContext (σ := σ) Γ := by
  simp [fvContext]

theorem mem_fvContext_iff {σ : Type} {x : Var} {Γ : List (Formula σ)} :
    x ∈ fvContext (σ := σ) Γ ↔ ∃ ψ, ψ ∈ Γ ∧ x ∈ Syntax.fvFormula ψ := by
  induction Γ with
  | nil =>
      simp [fvContext]
  | cons φ Γ ih =>
      simp [fvContext_cons, ih]

theorem fvContext_mono {σ : Type} {Γ Δ : List (Formula σ)} (hsub : Γ ⊆ Δ) :
    fvContext (σ := σ) Γ ⊆ fvContext (σ := σ) Δ := by
  intro x hx
  rcases (mem_fvContext_iff (σ := σ) (x := x) (Γ := Γ)).1 hx with ⟨ψ, hψ, hxψ⟩
  exact (mem_fvContext_iff (σ := σ) (x := x) (Γ := Δ)).2 ⟨ψ, hsub hψ, hxψ⟩

end ND

/--
Propositional derivability (`⊤ ⊥ ¬ ∧ ∨ →`), used for Kripke-style soundness/completeness results.

This intentionally excludes `sigma/pi` so propositional Kripke semantics can be stated without any
domain-of-quantification apparatus.
-/
inductive DerivesProp {σ : Type} : List (Formula σ) → Formula σ → Prop
  | hyp {Γ : List (Formula σ)} {φ : Formula σ} : φ ∈ Γ → DerivesProp Γ φ
  | topI {Γ : List (Formula σ)} : DerivesProp Γ .top
  | botE {Γ : List (Formula σ)} {φ : Formula σ} : DerivesProp Γ .bot → DerivesProp Γ φ
  | andI {Γ : List (Formula σ)} {φ ψ : Formula σ} :
      DerivesProp Γ φ → DerivesProp Γ ψ → DerivesProp Γ (.and φ ψ)
  | andEL {Γ : List (Formula σ)} {φ ψ : Formula σ} : DerivesProp Γ (.and φ ψ) → DerivesProp Γ φ
  | andER {Γ : List (Formula σ)} {φ ψ : Formula σ} : DerivesProp Γ (.and φ ψ) → DerivesProp Γ ψ
  | orIL {Γ : List (Formula σ)} {φ ψ : Formula σ} : DerivesProp Γ φ → DerivesProp Γ (.or φ ψ)
  | orIR {Γ : List (Formula σ)} {φ ψ : Formula σ} : DerivesProp Γ ψ → DerivesProp Γ (.or φ ψ)
  | orE {Γ : List (Formula σ)} {φ ψ χ : Formula σ} :
      DerivesProp Γ (.or φ ψ) → DerivesProp (φ :: Γ) χ → DerivesProp (ψ :: Γ) χ → DerivesProp Γ χ
  | impI {Γ : List (Formula σ)} {φ ψ : Formula σ} :
      DerivesProp (φ :: Γ) ψ → DerivesProp Γ (.imp φ ψ)
  | impE {Γ : List (Formula σ)} {φ ψ : Formula σ} :
      DerivesProp Γ (.imp φ ψ) → DerivesProp Γ φ → DerivesProp Γ ψ
  | notI {Γ : List (Formula σ)} {φ : Formula σ} :
      DerivesProp (φ :: Γ) .bot → DerivesProp Γ (.not φ)
  | notE {Γ : List (Formula σ)} {φ : Formula σ} :
      DerivesProp Γ (.not φ) → DerivesProp Γ φ → DerivesProp Γ .bot

namespace DerivesProp

variable {σ : Type}

theorem weaken {Γ : List (Formula σ)} {φ : Formula σ} :
    DerivesProp Γ φ → ∀ {Δ : List (Formula σ)}, Γ ⊆ Δ → DerivesProp Δ φ := by
  intro h Δ hsub
  induction h generalizing Δ with
  | hyp hmem =>
      exact DerivesProp.hyp (hsub hmem)
  | topI =>
      exact DerivesProp.topI
  | botE h ih =>
      exact DerivesProp.botE (ih (Δ := Δ) hsub)
  | andI h1 h2 ih1 ih2 =>
      exact DerivesProp.andI (ih1 (Δ := Δ) hsub) (ih2 (Δ := Δ) hsub)
  | andEL h ih =>
      exact DerivesProp.andEL (ih (Δ := Δ) hsub)
  | andER h ih =>
      exact DerivesProp.andER (ih (Δ := Δ) hsub)
  | orIL h ih =>
      exact DerivesProp.orIL (ih (Δ := Δ) hsub)
  | orIR h ih =>
      exact DerivesProp.orIR (ih (Δ := Δ) hsub)
  | orE hOr hφ hψ ihOr ihφ ihψ =>
      rename_i Γ φ ψ χ
      have hOr' : DerivesProp Δ (.or φ ψ) := ihOr (Δ := Δ) hsub
      have subφ : (φ :: Γ) ⊆ (φ :: Δ) := by
        intro θ hθ
        rcases List.mem_cons.1 hθ with rfl | hθ
        · simp
        · exact List.mem_cons_of_mem _ (hsub hθ)
      have subψ : (ψ :: Γ) ⊆ (ψ :: Δ) := by
        intro θ hθ
        rcases List.mem_cons.1 hθ with rfl | hθ
        · simp
        · exact List.mem_cons_of_mem _ (hsub hθ)
      have hφ' : DerivesProp (φ :: Δ) χ := ihφ (Δ := φ :: Δ) subφ
      have hψ' : DerivesProp (ψ :: Δ) χ := ihψ (Δ := ψ :: Δ) subψ
      exact DerivesProp.orE hOr' hφ' hψ'
  | impI h ih =>
      rename_i Γ φ ψ
      have sub : (φ :: Γ) ⊆ (φ :: Δ) := by
        intro θ hθ
        rcases List.mem_cons.1 hθ with rfl | hθ
        · simp
        · exact List.mem_cons_of_mem _ (hsub hθ)
      exact DerivesProp.impI (ih (Δ := φ :: Δ) sub)
  | impE h1 h2 ih1 ih2 =>
      exact DerivesProp.impE (ih1 (Δ := Δ) hsub) (ih2 (Δ := Δ) hsub)
  | notI h ih =>
      rename_i Γ φ
      have sub : (φ :: Γ) ⊆ (φ :: Δ) := by
        intro θ hθ
        rcases List.mem_cons.1 hθ with rfl | hθ
        · simp
        · exact List.mem_cons_of_mem _ (hsub hθ)
      exact DerivesProp.notI (ih (Δ := φ :: Δ) sub)
  | notE h1 h2 ih1 ih2 =>
      exact DerivesProp.notE (ih1 (Δ := Δ) hsub) (ih2 (Δ := Δ) hsub)

end DerivesProp

/-- Derivability: `Derives Γ φ` means φ is derivable from assumptions Γ. -/
inductive Derives {σ : Type} : List (Formula σ) → Formula σ → Prop
  | hyp {Γ : List (Formula σ)} {φ : Formula σ} : φ ∈ Γ → Derives Γ φ
  | topI {Γ : List (Formula σ)} : Derives Γ .top
  | botE {Γ : List (Formula σ)} {φ : Formula σ} : Derives Γ .bot → Derives Γ φ
  | andI {Γ : List (Formula σ)} {φ ψ : Formula σ} : Derives Γ φ → Derives Γ ψ → Derives Γ (.and φ ψ)
  | andEL {Γ : List (Formula σ)} {φ ψ : Formula σ} : Derives Γ (.and φ ψ) → Derives Γ φ
  | andER {Γ : List (Formula σ)} {φ ψ : Formula σ} : Derives Γ (.and φ ψ) → Derives Γ ψ
  | orIL {Γ : List (Formula σ)} {φ ψ : Formula σ} : Derives Γ φ → Derives Γ (.or φ ψ)
  | orIR {Γ : List (Formula σ)} {φ ψ : Formula σ} : Derives Γ ψ → Derives Γ (.or φ ψ)
  | orE {Γ : List (Formula σ)} {φ ψ χ : Formula σ} :
      Derives Γ (.or φ ψ) → Derives (φ :: Γ) χ → Derives (ψ :: Γ) χ → Derives Γ χ
  | impI {Γ : List (Formula σ)} {φ ψ : Formula σ} : Derives (φ :: Γ) ψ → Derives Γ (.imp φ ψ)
  | impE {Γ : List (Formula σ)} {φ ψ : Formula σ} : Derives Γ (.imp φ ψ) → Derives Γ φ → Derives Γ ψ
  | notI {Γ : List (Formula σ)} {φ : Formula σ} : Derives (φ :: Γ) .bot → Derives Γ (.not φ)
  | notE {Γ : List (Formula σ)} {φ : Formula σ} : Derives Γ (.not φ) → Derives Γ φ → Derives Γ .bot
  -- Quantifiers (`sigma` / `pi`) use capture-avoiding substitution (`Syntax.substFormula`).
  -- Hence `piE`/`sigmaI` need no extra side conditions; hygiene is internal to substitution.
  | piI {Γ : List (Formula σ)} {x a : Var} {φ : Formula σ} :
      a ∉ ND.fvContext Γ →
      a ∉ Syntax.varsFormula φ →
      Derives Γ (Syntax.substFormula (σ := σ) x (.var a) φ) →
      Derives Γ (.pi x φ)
  | piE {Γ : List (Formula σ)} {x a : Var} {φ : Formula σ} :
      Derives Γ (.pi x φ) →
      Derives Γ (Syntax.substFormula (σ := σ) x (.var a) φ)
  | sigmaI {Γ : List (Formula σ)} {x a : Var} {φ : Formula σ} :
      Derives Γ (Syntax.substFormula (σ := σ) x (.var a) φ) →
      Derives Γ (.sigma x φ)
  | sigmaE {Γ : List (Formula σ)} {x a : Var} {φ χ : Formula σ} :
      Derives Γ (.sigma x φ) →
      a ∉ ND.fvContext Γ →
      a ∉ Syntax.varsFormula φ →
      a ∉ Syntax.fvFormula χ →
      Derives (Syntax.substFormula (σ := σ) x (.var a) φ :: Γ) χ →
      Derives Γ χ
  | wk {Γ Δ : List (Formula σ)} {φ : Formula σ} :
      Derives Γ φ →
      Γ ⊆ Δ →
      Derives Δ φ

namespace Derives

variable {σ : Type}

theorem ofDerivesProp {Γ : List (Formula σ)} {φ : Formula σ} :
    DerivesProp (σ := σ) Γ φ → Derives (σ := σ) Γ φ := by
  intro h
  induction h with
  | hyp hmem =>
      exact Derives.hyp hmem
  | topI =>
      exact Derives.topI
  | botE h ih =>
      exact Derives.botE ih
  | andI h1 h2 ih1 ih2 =>
      exact Derives.andI ih1 ih2
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
  | impE h1 h2 ih1 ih2 =>
      exact Derives.impE ih1 ih2
  | notI h ih =>
      exact Derives.notI ih
  | notE h1 h2 ih1 ih2 =>
      exact Derives.notE ih1 ih2

theorem weaken {Γ : List (Formula σ)} {φ : Formula σ} :
    Derives Γ φ →
      ∀ {Δ : List (Formula σ)},
        Γ ⊆ Δ →
        (ND.fvContext Δ ⊆ ND.fvContext Γ) →
        Derives Δ φ := by
  intro h Δ hsub _hfv
  exact Derives.wk h hsub

theorem pi_instance_change_witness
    {Γ : List (Formula σ)} {x a b : Var} {φ : Formula σ}
    (haΓ : a ∉ ND.fvContext (σ := σ) Γ)
    (haVars : a ∉ Syntax.varsFormula (σ := σ) φ)
    (_hbBound : b ∉ Syntax.boundVars (σ := σ) φ)
    (h : Derives (σ := σ) Γ (Syntax.substFormula (σ := σ) x (.var a) φ)) :
    Derives (σ := σ) Γ (Syntax.substFormula (σ := σ) x (.var b) φ) := by
  have hPi : Derives (σ := σ) Γ (.pi x φ) := Derives.piI haΓ haVars h
  exact Derives.piE hPi

theorem sigma_from_instance
    {Γ : List (Formula σ)} {x a : Var} {φ : Formula σ}
    (_haBound : a ∉ Syntax.boundVars (σ := σ) φ)
    (h : Derives (σ := σ) Γ (Syntax.substFormula (σ := σ) x (.var a) φ)) :
    Derives (σ := σ) Γ (.sigma x φ) := by
  exact Derives.sigmaI h

theorem sigma_elim_hyp
    {Γ : List (Formula σ)} {x a : Var} {φ χ : Formula σ}
    (hSigma : Derives (σ := σ) Γ (.sigma x φ))
    (haΓ : a ∉ ND.fvContext (σ := σ) Γ)
    (haVars : a ∉ Syntax.varsFormula (σ := σ) φ)
    (haχ : a ∉ Syntax.fvFormula (σ := σ) χ)
    (hHyp : Derives (σ := σ) (Syntax.substFormula (σ := σ) x (.var a) φ :: Γ) χ) :
    Derives (σ := σ) Γ χ := by
  exact Derives.sigmaE hSigma haΓ haVars haχ hHyp

/--
Weakening by a single **closed** assumption is always admissible for `Derives`.

This is the key unconditional weakening variant used when extending contexts in
metatheory without introducing new free variables that could violate eigenvariable freshness.
-/
theorem weaken_cons_closed
    {Γ : List (Formula σ)} {φ ψ : Formula σ}
    (hDer : Derives (σ := σ) Γ φ)
    (hClosed : Syntax.fvFormula (σ := σ) ψ = ∅) :
    Derives (σ := σ) (ψ :: Γ) φ := by
  refine Derives.weaken (σ := σ) hDer (Δ := ψ :: Γ) ?_ ?_
  · intro θ hθ
    exact List.mem_cons_of_mem _ hθ
  · intro x hx
    have hsplit : x ∈ Syntax.fvFormula (σ := σ) ψ ∨ x ∈ ND.fvContext (σ := σ) Γ := by
      simpa [ND.fvContext] using hx
    cases hsplit with
    | inl hleft =>
        exfalso
        simp [hClosed] at hleft
    | inr hright =>
        exact hright

/--
Weakening by a list of closed assumptions is admissible for `Derives`.
-/
theorem weaken_append_closed
    {Γ Δ : List (Formula σ)} {φ : Formula σ}
    (hDer : Derives (σ := σ) Γ φ)
    (hClosed : ∀ ψ, ψ ∈ Δ → Syntax.fvFormula (σ := σ) ψ = ∅) :
    Derives (σ := σ) (Δ ++ Γ) φ := by
  induction Δ with
  | nil =>
      simpa using hDer
  | cons ψ Δ ih =>
      have hClosedHead : Syntax.fvFormula (σ := σ) ψ = ∅ := hClosed ψ (by simp)
      have hClosedTail : ∀ θ, θ ∈ Δ → Syntax.fvFormula (σ := σ) θ = ∅ := by
        intro θ hθ
        exact hClosed θ (by simp [hθ])
      have hTail : Derives (σ := σ) (Δ ++ Γ) φ := ih hClosedTail
      simpa [List.cons_append] using
        (weaken_cons_closed (σ := σ) (Γ := Δ ++ Γ) (φ := φ) (ψ := ψ) hTail hClosedHead)

end Derives

end Noneism
end HeytingLean
