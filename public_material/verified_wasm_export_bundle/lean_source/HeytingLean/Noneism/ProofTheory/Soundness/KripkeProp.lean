import HeytingLean.Noneism.ProofTheory.ND
import HeytingLean.Noneism.Semantics.KripkeProp

/-!
# Noneism.ProofTheory.Soundness.KripkeProp

Soundness of the ND proof system (`Noneism.ProofTheory.ND`) with respect to the propositional
Kripke semantics (`Noneism.Semantics.KripkeProp`).

This soundness theorem targets the **propositional** proof system `DerivesProp` (no `sigma/pi`).
Completeness for the propositional fragment is handled separately.
-/

namespace HeytingLean
namespace Noneism

open Formula

namespace KripkeProp

open KripkeProp

variable {σ : Type}

/-! ## Persistence -/

/-- Forcing is persistent (monotone) along the preorder of worlds. -/
theorem forces_mono {W : Type} [Preorder W] (M : Model W σ) :
    ∀ {w v : W}, w ≤ v → ∀ {φ : Formula σ}, Forces M w φ → Forces M v φ := by
  intro w v hwv φ
  induction φ generalizing w v with
  | top =>
      intro _; trivial
  | bot =>
      intro h; cases h
  | pred p args =>
      intro h; exact M.monoPred hwv p args h
  | eExists t =>
      intro h; exact M.monoEx hwv t h
  | not φ ih =>
      intro hNot u hvu huφ
      have hwu : w ≤ u := le_trans hwv hvu
      exact hNot u hwu huφ
  | and φ ψ ihφ ihψ =>
      intro hAnd
      exact And.intro (ihφ hwv hAnd.1) (ihψ hwv hAnd.2)
  | or φ ψ ihφ ihψ =>
      intro hOr
      cases hOr with
      | inl h => exact Or.inl (ihφ hwv h)
      | inr h => exact Or.inr (ihψ hwv h)
  | imp φ ψ ihφ ihψ =>
      intro hImp u hvu huφ
      have hwu : w ≤ u := le_trans hwv hvu
      exact hImp u hwu huφ
  | sigma x φ ih =>
      intro h; cases h
  | pi x φ ih =>
      intro h; cases h

/-! ## Soundness -/

theorem soundness {Γ : List (Formula σ)} {φ : Formula σ} :
    DerivesProp (σ := σ) Γ φ → Entails (σ := σ) Γ φ := by
  intro hDer
  induction hDer with
  | hyp hmem =>
      intro W _ M w hw
      exact hw _ hmem
  | topI =>
      intro W _ M w _
      simp [Forces]
  | botE h ih =>
      intro W _ M w hw
      have hbot : Forces M w (.bot : Formula σ) := ih (W := W) (M := M) (w := w) hw
      -- `Forces` at `.bot` reduces definitionally to `False`.
      cases (show False from hbot)
  | andI h1 h2 ih1 ih2 =>
      intro W _ M w hw
      exact And.intro (ih1 (W := W) (M := M) (w := w) hw) (ih2 (W := W) (M := M) (w := w) hw)
  | andEL h ih =>
      intro W _ M w hw
      have : Forces M w (.and _ _ : Formula σ) := ih (W := W) (M := M) (w := w) hw
      exact this.1
  | andER h ih =>
      intro W _ M w hw
      have : Forces M w (.and _ _ : Formula σ) := ih (W := W) (M := M) (w := w) hw
      exact this.2
  | orIL h ih =>
      intro W _ M w hw
      exact Or.inl (ih (W := W) (M := M) (w := w) hw)
  | orIR h ih =>
      intro W _ M w hw
      exact Or.inr (ih (W := W) (M := M) (w := w) hw)
  | orE h h1 h2 ih ih1 ih2 =>
      rename_i Γ φ ψ χ
      intro W _ M w hw
      have : Forces M w (.or _ _ : Formula σ) := ih (W := W) (M := M) (w := w) hw
      cases this with
      | inl hφw =>
          have hw' : ∀ θ ∈ (φ :: Γ), Forces M w θ := by
            intro θ hθ
            rcases List.mem_cons.1 hθ with rfl | hθ
            · exact hφw
            · exact hw θ hθ
          exact ih1 (W := W) (M := M) (w := w) hw'
      | inr hψw =>
          have hw' : ∀ θ ∈ (ψ :: Γ), Forces M w θ := by
            intro θ hθ
            rcases List.mem_cons.1 hθ with rfl | hθ
            · exact hψw
            · exact hw θ hθ
          exact ih2 (W := W) (M := M) (w := w) hw'
  | impI h ih =>
      rename_i Γ φ ψ
      intro W _ M w hw v hwv hvφ
      have hwvΓ : ∀ θ ∈ Γ, Forces M v θ := by
        intro θ hθ
        exact forces_mono (M := M) (w := w) (v := v) hwv (φ := θ) (hw θ hθ)
      have hw' : ∀ θ ∈ (φ :: Γ), Forces M v θ := by
        intro θ hθ
        rcases List.mem_cons.1 hθ with rfl | hθ
        · exact hvφ
        · exact hwvΓ θ hθ
      exact ih (W := W) (M := M) (w := v) hw'
  | impE h1 h2 ih1 ih2 =>
      rename_i Γ φ ψ
      intro W _ M w hw
      have himp : Forces M w (.imp φ ψ) := ih1 (W := W) (M := M) (w := w) hw
      have hφw : Forces M w φ := ih2 (W := W) (M := M) (w := w) hw
      exact himp w le_rfl hφw
  | notI h ih =>
      rename_i Γ φ
      intro W _ M w hw v hwv hvφ
      have hwvΓ : ∀ θ ∈ Γ, Forces M v θ := by
        intro θ hθ
        exact forces_mono (M := M) (w := w) (v := v) hwv (φ := θ) (hw θ hθ)
      have hw' : ∀ θ ∈ (φ :: Γ), Forces M v θ := by
        intro θ hθ
        rcases List.mem_cons.1 hθ with rfl | hθ
        · exact hvφ
        · exact hwvΓ θ hθ
      have hbot : Forces M v (.bot : Formula σ) := ih (W := W) (M := M) (w := v) hw'
      cases (show False from hbot)
  | notE h1 h2 ih1 ih2 =>
      rename_i Γ φ
      intro W _ M w hw
      have hnot : Forces M w (.not φ) := ih1 (W := W) (M := M) (w := w) hw
      have hφw : Forces M w φ := ih2 (W := W) (M := M) (w := w) hw
      exact (hnot w le_rfl hφw).elim

end KripkeProp

end Noneism
end HeytingLean
