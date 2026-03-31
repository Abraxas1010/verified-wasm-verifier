import HeytingLean.Noneism.Semantics.KripkeFO
import HeytingLean.Noneism.ProofTheory.ND
import HeytingLean.Noneism.ProofTheory.Soundness.KripkeFO
import HeytingLean.Noneism.Syntax.Subst

/-!
# Noneism.ProofTheory.Quantifiers.UniversalClosure

Utilities for universally closing formulas over an explicit variable list.

This file is a foundational helper for sentence-route completeness reductions:
`closeAll xs φ` is `forall xs, φ` with right-associated binders.
-/

namespace HeytingLean
namespace Noneism
namespace Quantifiers

open Formula

variable {σ : Type}

/-- Right-associated universal closure over an explicit variable list. -/
def closeAll : List Var -> Formula σ -> Formula σ
  | [], φ => φ
  | x :: xs, φ => .pi x (closeAll xs φ)

@[simp] theorem closeAll_nil (φ : Formula σ) :
    closeAll (σ := σ) [] φ = φ := rfl

@[simp] theorem closeAll_cons (x : Var) (xs : List Var) (φ : Formula σ) :
    closeAll (σ := σ) (x :: xs) φ = .pi x (closeAll (σ := σ) xs φ) := rfl

/-- Canonical closure using the free-variable set of the formula. -/
noncomputable def closeFormula (φ : Formula σ) : Formula σ :=
  closeAll (σ := σ) (Syntax.fvFormula (σ := σ) φ).toList φ

/-- Pointwise closure for an assumption context. -/
noncomputable def closeContext (Γ : List (Formula σ)) : List (Formula σ) :=
  Γ.map (closeFormula (σ := σ))

/-- Right-associated implication chain encoding of a sequent context. -/
def impChain : List (Formula σ) -> Formula σ -> Formula σ
  | [], φ => φ
  | ψ :: Γ, φ => .imp ψ (impChain Γ φ)

@[simp] theorem impChain_nil (φ : Formula σ) :
    impChain (σ := σ) [] φ = φ := rfl

@[simp] theorem impChain_cons (ψ : Formula σ) (Γ : List (Formula σ)) (φ : Formula σ) :
    impChain (σ := σ) (ψ :: Γ) φ = .imp ψ (impChain (σ := σ) Γ φ) := rfl

/-- Free vars only shrink under universal closure. -/
theorem fv_closeAll_subset (xs : List Var) (φ : Formula σ) :
    Syntax.fvFormula (σ := σ) (closeAll (σ := σ) xs φ) ⊆
      Syntax.fvFormula (σ := σ) φ := by
  induction xs generalizing φ with
  | nil =>
      simp [closeAll]
  | cons x xs ih =>
      intro y hy
      have hy' : y ∈ (Syntax.fvFormula (σ := σ) (closeAll (σ := σ) xs φ)).erase x := by
        simpa [closeAll, Syntax.fvFormula, Finset.mem_erase] using hy
      have hyIn : y ∈ Syntax.fvFormula (σ := σ) (closeAll (σ := σ) xs φ) :=
        (Finset.mem_erase.1 hy').2
      exact ih _ hyIn

/--
If a variable survives `closeAll xs`, it was free in the original formula and was not quantified
by the closure list.
-/
theorem mem_fv_closeAll_implies_mem_and_not_mem
    {x : Var} (xs : List Var) (φ : Formula σ)
    (hx : x ∈ Syntax.fvFormula (σ := σ) (closeAll (σ := σ) xs φ)) :
    x ∈ Syntax.fvFormula (σ := σ) φ ∧ x ∉ xs := by
  induction xs generalizing φ with
  | nil =>
      simp [closeAll] at hx
      exact ⟨hx, by simp⟩
  | cons y ys ih =>
      have hxErase : x ∈ (Syntax.fvFormula (σ := σ) (closeAll (σ := σ) ys φ)).erase y := by
        simpa [closeAll, Syntax.fvFormula, Finset.mem_erase] using hx
      have hxy : x ≠ y := (Finset.mem_erase.1 hxErase).1
      have hxTail : x ∈ Syntax.fvFormula (σ := σ) (closeAll (σ := σ) ys φ) :=
        (Finset.mem_erase.1 hxErase).2
      rcases ih _ hxTail with ⟨hxBase, hxNotYs⟩
      exact ⟨hxBase, by simp [hxy, hxNotYs]⟩

/-- `closeFormula` is always closed. -/
theorem fv_closeFormula_eq_empty (φ : Formula σ) :
    Syntax.fvFormula (σ := σ) (closeFormula (σ := σ) φ) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.2
  intro x hx
  rcases mem_fv_closeAll_implies_mem_and_not_mem
    (σ := σ) (x := x) (xs := (Syntax.fvFormula (σ := σ) φ).toList) (φ := φ) hx with
    ⟨hxBase, hxNotList⟩
  have hxList : x ∈ (Syntax.fvFormula (σ := σ) φ).toList := by
    simpa using hxBase
  exact hxNotList hxList

@[simp] theorem closeFormula_eq_self_of_fv_empty
    (φ : Formula σ)
    (hφ : Syntax.fvFormula (σ := σ) φ = ∅) :
    closeFormula (σ := σ) φ = φ := by
  unfold closeFormula
  simp [hφ]

theorem closeContext_eq_self_of_closed
    (Γ : List (Formula σ))
    (hΓClosed : ∀ ψ, ψ ∈ Γ -> Syntax.fvFormula (σ := σ) ψ = ∅) :
    closeContext (σ := σ) Γ = Γ := by
  induction Γ with
  | nil =>
      simp [closeContext]
  | cons ψ Γ ih =>
      have hψ : Syntax.fvFormula (σ := σ) ψ = ∅ := hΓClosed ψ (by simp)
      have hΓClosedTail : ∀ θ, θ ∈ Γ -> Syntax.fvFormula (σ := σ) θ = ∅ := by
        intro θ hθ
        exact hΓClosed θ (by simp [hθ])
      simpa [closeContext, closeFormula_eq_self_of_fv_empty (σ := σ) ψ hψ] using
        ih hΓClosedTail

/-- Eliminate a universal closure list by instantiating each binder with itself. -/
theorem derives_of_closeAll
    (Γ : List (Formula σ)) (xs : List Var) (φ : Formula σ) :
    Derives (σ := σ) Γ (closeAll (σ := σ) xs φ) →
      Derives (σ := σ) Γ φ := by
  intro h
  induction xs generalizing φ with
  | nil =>
      simpa [closeAll] using h
  | cons x xs ih =>
      have hTail :
          Derives (σ := σ) Γ (closeAll (σ := σ) xs φ) := by
        have hInst :
            Derives (σ := σ) Γ
              (Syntax.substFormula (σ := σ) x (.var x) (closeAll (σ := σ) xs φ)) :=
          Derives.piE (x := x) (a := x) h
        simpa [Syntax.substFormula_var_self] using hInst
      exact ih (φ := φ) hTail

/-- A closed formula assumption can always be instantiated back to the original formula. -/
theorem derives_of_closeFormula
    (Γ : List (Formula σ)) (φ : Formula σ) :
    Derives (σ := σ) Γ (closeFormula (σ := σ) φ) →
      Derives (σ := σ) Γ φ := by
  intro h
  simpa [closeFormula] using
    (derives_of_closeAll (σ := σ) Γ (Syntax.fvFormula (σ := σ) φ).toList φ h)

/-- Every formula in `closeContext` is closed, so the whole context has empty free-variable set. -/
theorem fvContext_closeContext_eq_empty (Γ : List (Formula σ)) :
    ND.fvContext (σ := σ) (closeContext (σ := σ) Γ) = ∅ := by
  unfold closeContext ND.fvContext
  induction Γ with
  | nil =>
      simp
  | cons φ Γ ih =>
      simp [fv_closeFormula_eq_empty, ih]

/--
Any original assumption can be recovered from `closeContext` by hypothesis + closure elimination.
-/
theorem derives_of_mem_closeContext
    {Γ : List (Formula σ)} {ψ : Formula σ}
    (hψ : ψ ∈ Γ) :
    Derives (σ := σ) (closeContext (σ := σ) Γ) ψ := by
  have hCloseMem :
      closeFormula (σ := σ) ψ ∈ closeContext (σ := σ) Γ := by
    exact List.mem_map.mpr ⟨ψ, hψ, rfl⟩
  exact derives_of_closeFormula
    (σ := σ)
    (Γ := closeContext (σ := σ) Γ)
    (φ := ψ)
    (Derives.hyp hCloseMem)

/--
Decode an implication-chain theorem inside an extended context.

If `(Γ ++ Δ) ⊢ impChain Γ φ`, then `(Γ ++ Δ) ⊢ φ`.
-/
theorem derives_of_impChain_at
    (Γ Δ : List (Formula σ)) (φ : Formula σ) :
    Derives (σ := σ) (Γ ++ Δ) (impChain (σ := σ) Γ φ) →
      Derives (σ := σ) (Γ ++ Δ) φ := by
  induction Γ generalizing Δ with
  | nil =>
      intro h
      simpa [impChain] using h
  | cons ψ Γ ih =>
      intro h
      have hψ :
          Derives (σ := σ) ((ψ :: Γ) ++ Δ) ψ :=
        Derives.hyp (by simp)
      have hTail :
          Derives (σ := σ) ((ψ :: Γ) ++ Δ) (impChain (σ := σ) Γ φ) :=
        Derives.impE h hψ
      have hSubForward :
          ((ψ :: Γ) ++ Δ) ⊆ (Γ ++ (ψ :: Δ)) := by
        intro θ hθ
        have hCases : θ = ψ ∨ θ ∈ Γ ∨ θ ∈ Δ := by
          simpa [List.mem_append, or_left_comm, or_assoc] using hθ
        rcases hCases with rfl | hθΓ | hθΔ
        · simp [List.mem_append]
        · simp [List.mem_append, hθΓ]
        · simp [List.mem_append, hθΔ]
      have hSubBackward :
          (Γ ++ (ψ :: Δ)) ⊆ ((ψ :: Γ) ++ Δ) := by
        intro θ hθ
        have hCases : θ ∈ Γ ∨ θ = ψ ∨ θ ∈ Δ := by
          simpa [List.mem_append, or_left_comm, or_assoc] using hθ
        rcases hCases with hθΓ | rfl | hθΔ
        · simp [List.mem_append, hθΓ]
        · simp [List.mem_append]
        · simp [List.mem_append, hθΔ]
      have hTail' :
          Derives (σ := σ) (Γ ++ (ψ :: Δ)) (impChain (σ := σ) Γ φ) :=
        Derives.wk hTail hSubForward
      have hCore :
          Derives (σ := σ) (Γ ++ (ψ :: Δ)) φ :=
        ih (Δ := ψ :: Δ) hTail'
      exact Derives.wk hCore hSubBackward

/--
Decode an implication-chain theorem at top-level.

If `[] ⊢ impChain Γ φ`, then `Γ ⊢ φ`.
-/
theorem derives_of_impChain_nil
    (Γ : List (Formula σ)) (φ : Formula σ) :
    Derives (σ := σ) [] (impChain (σ := σ) Γ φ) →
      Derives (σ := σ) Γ φ := by
  intro h
  have hΓ : Derives (σ := σ) (Γ ++ []) (impChain (σ := σ) Γ φ) := by
    exact Derives.wk h (by
      intro ψ hψ
      exact False.elim (by cases hψ))
  simpa using derives_of_impChain_at (σ := σ) Γ [] φ hΓ

namespace KripkeFO

open HeytingLean.Noneism.KripkeFO

variable {W : Type} [Preorder W] {D : Type}

@[simp] theorem forces_closeAll_nil
    (M : Model W σ D) (ρ : Valuation D) (w : W) (φ : Formula σ) :
    Forces M ρ w (closeAll (σ := σ) [] φ) ↔ Forces M ρ w φ := Iff.rfl

@[simp] theorem forces_closeAll_cons
    (M : Model W σ D) (ρ : Valuation D) (w : W)
    (x : Var) (xs : List Var) (φ : Formula σ) :
    Forces M ρ w (closeAll (σ := σ) (x :: xs) φ) ↔
      (∀ v : W, w ≤ v -> ∀ d : D,
        Forces M (update ρ x d) v (closeAll (σ := σ) xs φ)) := Iff.rfl

/-- Eliminate universal closure semantically by instantiating binders with the current valuation. -/
theorem forces_of_closeAll
    (M : Model W σ D) (ρ : Valuation D) (w : W)
    (xs : List Var) (φ : Formula σ) :
    Forces M ρ w (closeAll (σ := σ) xs φ) →
      Forces M ρ w φ := by
  intro hClose
  induction xs generalizing ρ w with
  | nil =>
      simpa [closeAll] using hClose
  | cons x xs ih =>
      have hTail :
          Forces M (update ρ x (ρ x)) w (closeAll (σ := σ) xs φ) :=
        hClose w (le_rfl) (ρ x)
      have hUpdate : update ρ x (ρ x) = ρ := by
        funext y
        by_cases hy : y = x
        · subst hy
          simp [update]
        · simp [update, hy]
      have hTail' : Forces M ρ w (closeAll (σ := σ) xs φ) := by
        simpa [hUpdate] using hTail
      exact ih (ρ := ρ) (w := w) hTail'

/-- A closed formula assumption always yields the original formula semantically. -/
theorem forces_of_closeFormula
    (M : Model W σ D) (ρ : Valuation D) (w : W) (φ : Formula σ) :
    Forces M ρ w (closeFormula (σ := σ) φ) →
      Forces M ρ w φ := by
  intro hClose
  exact forces_of_closeAll (σ := σ) (M := M) (ρ := ρ) (w := w)
    ((Syntax.fvFormula (σ := σ) φ).toList) φ hClose

/--
Entailment transport from an open assumption context to its universally closed context.

`closeContext Γ` is semantically stronger than `Γ`, so any consequence of `Γ` is also a
consequence of `closeContext Γ`.
-/
theorem entails_of_entails_closeContext
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hEnt : Entails (σ := σ) Γ φ) :
    Entails (σ := σ) (closeContext (σ := σ) Γ) φ := by
  intro W _ D M ρ w hClosed
  have hOpen : ∀ ψ ∈ Γ, Forces M ρ w ψ := by
    intro ψ hψ
    have hCloseMem :
        closeFormula (σ := σ) ψ ∈ closeContext (σ := σ) Γ := by
      exact List.mem_map.mpr ⟨ψ, hψ, rfl⟩
    have hClose : Forces M ρ w (closeFormula (σ := σ) ψ) := hClosed _ hCloseMem
    exact forces_of_closeFormula (σ := σ) (M := M) (ρ := ρ) (w := w) ψ hClose
  exact hEnt (W := W) (D := D) (M := M) (ρ := ρ) (w := w) hOpen

/--
If assumptions are closed, entailment lifts through universal closure of the conclusion.
-/
theorem entails_closeAll_of_entails_closedAssumptions
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓClosed : ∀ ψ, ψ ∈ Γ → Syntax.fvFormula (σ := σ) ψ = ∅)
    (hEnt : Entails (σ := σ) Γ φ) :
    ∀ xs : List Var, Entails (σ := σ) Γ (closeAll (σ := σ) xs φ) := by
  intro xs
  induction xs with
  | nil =>
      simpa [closeAll] using hEnt
  | cons x xs ih =>
      intro W _ D M ρ w hΓ v hwv d
      have hΓvUpd : ∀ ψ ∈ Γ, Forces M (update ρ x d) v ψ := by
        intro ψ hψ
        have hψw : Forces M ρ w ψ := hΓ ψ hψ
        have hψv : Forces M ρ v ψ :=
          forces_mono (σ := σ) (M := M) (ρ := ρ) hwv hψw
        have hxNotFv : x ∉ Syntax.fvFormula (σ := σ) ψ := by
          rw [hΓClosed ψ hψ]
          simp
        exact (forces_update_of_not_mem_fvFormula
          (σ := σ) (M := M) (ρ := ρ) (y := x) (d := d) ψ hxNotFv v).2 hψv
      exact ih (W := W) (D := D) (M := M) (ρ := update ρ x d) (w := v) hΓvUpd

/-- Closed-assumption specialization of `entails_closeAll_of_entails_closedAssumptions`. -/
theorem entails_closeFormula_of_entails_closedAssumptions
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓClosed : ∀ ψ, ψ ∈ Γ → Syntax.fvFormula (σ := σ) ψ = ∅)
    (hEnt : Entails (σ := σ) Γ φ) :
    Entails (σ := σ) Γ (closeFormula (σ := σ) φ) := by
  simpa [closeFormula] using
    (entails_closeAll_of_entails_closedAssumptions
      (σ := σ)
      (Γ := Γ)
      (φ := φ)
      hΓClosed hEnt
      ((Syntax.fvFormula (σ := σ) φ).toList))

/--
Combined transport: any entailment lifts to closed assumptions + closed conclusion.

This packages the open-to-sentence semantic reduction step needed by the sentence-route
completeness pipeline.
-/
theorem entails_closeContext_closeFormula_of_entails
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hEnt : Entails (σ := σ) Γ φ) :
    Entails (σ := σ) (closeContext (σ := σ) Γ) (closeFormula (σ := σ) φ) := by
  refine entails_closeFormula_of_entails_closedAssumptions
    (σ := σ)
    (Γ := closeContext (σ := σ) Γ)
    (φ := φ)
    ?_
    (entails_of_entails_closeContext (σ := σ) (Γ := Γ) (φ := φ) hEnt)
  intro ψ hψ
  -- We use the direct closure lemma from `closeFormula` by map-membership witness.
  rcases List.mem_map.mp hψ with ⟨θ, hθΓ, hEq⟩
  subst hEq
  exact fv_closeFormula_eq_empty (σ := σ) θ

/--
Semantic sequent encoding: from a persistent local consequence relation at `w`,
obtain forcing of the implication-chain encoding at `w`.
-/
theorem forces_impChain_of_local_consequence
    {W : Type} [Preorder W] {D : Type}
    (M : Model W σ D) (ρ : Valuation D)
    (w : W) (Γ : List (Formula σ)) (φ : Formula σ)
    (hLocal :
      ∀ v : W,
        w ≤ v →
        (∀ ψ, ψ ∈ Γ → Forces M ρ v ψ) →
        Forces M ρ v φ) :
    Forces M ρ w (impChain (σ := σ) Γ φ) := by
  induction Γ generalizing w with
  | nil =>
      simpa [impChain] using hLocal w (le_rfl) (by intro ψ hψ; cases hψ)
  | cons ψ Γ ih =>
      intro v hwv hψv
      have hLocal' :
          ∀ u : W,
            v ≤ u →
            (∀ θ, θ ∈ Γ → Forces M ρ u θ) →
            Forces M ρ u φ := by
        intro u hvu hΓu
        have hψu : Forces M ρ u ψ :=
          forces_mono (σ := σ) (M := M) (ρ := ρ) hvu hψv
        have hAll : ∀ θ, θ ∈ (ψ :: Γ) → Forces M ρ u θ := by
          intro θ hθ
          rcases List.mem_cons.1 hθ with rfl | hθΓ
          · exact hψu
          · exact hΓu θ hθΓ
        exact hLocal u (le_trans hwv hvu) hAll
      exact ih (w := v) hLocal'

/--
Semantic implication-chain encoding of entailment:
`Γ ⊨ φ` implies `[] ⊨ impChain Γ φ`.
-/
theorem entails_nil_impChain_of_entails
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hEnt : Entails (σ := σ) Γ φ) :
    Entails (σ := σ) [] (impChain (σ := σ) Γ φ) := by
  intro W _ D M ρ w _hNil
  refine forces_impChain_of_local_consequence
    (σ := σ) (M := M) (ρ := ρ) (w := w) (Γ := Γ) (φ := φ) ?_
  intro v _hwv hΓv
  exact hEnt (W := W) (D := D) (M := M) (ρ := ρ) (w := v) hΓv

end KripkeFO
end Quantifiers
end Noneism
end HeytingLean
