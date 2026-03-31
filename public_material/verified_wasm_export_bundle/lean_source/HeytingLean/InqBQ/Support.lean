import HeytingLean.InqBQ.Models

namespace HeytingLean
namespace InqBQ

open Classical
open Set

variable {sig : Signature}

/-- Inquisitive support semantics for information states. -/
def supports (M : InfoModel sig) (s : Set M.W) (g : Assignment M.D) : Formula sig → Prop
  | .pred P ts =>
      ∀ w, w ∈ s → M.predInterp w P (fun i => denote M w g (ts i))
  | .eq t u =>
      ∀ w, w ∈ s → M.localEq w (denote M w g t) (denote M w g u)
  | .bot =>
      s = ∅
  | .conj φ ψ =>
      supports M s g φ ∧ supports M s g ψ
  | .inqDisj φ ψ =>
      supports M s g φ ∨ supports M s g ψ
  | .imp φ ψ =>
      ∀ t : Set M.W, t ⊆ s → supports M t g φ → supports M t g ψ
  | .forall_ x φ =>
      ∀ d : M.D, supports M s (Assignment.update g x d) φ
  | .inqExists x φ =>
      ∃ d : M.D, supports M s (Assignment.update g x d) φ

/-- Truth at a single world. -/
def holdsAt (M : InfoModel sig) (w : M.W) (g : Assignment M.D) (φ : Formula sig) : Prop :=
  supports M ({w} : Set M.W) g φ

/-- Global support over the entire world set. -/
def globallySupports (M : InfoModel sig) (g : Assignment M.D) (φ : Formula sig) : Prop :=
  supports M Set.univ g φ

theorem supports_mono (M : InfoModel sig) {s t : Set M.W} {g : Assignment M.D} :
    ∀ {φ : Formula sig}, supports M s g φ → t ⊆ s → supports M t g φ
  | .pred _ _, h, hts => by
      intro w hw
      exact h w (hts hw)
  | .eq _ _, h, hts => by
      intro w hw
      exact h w (hts hw)
  | .bot, h, hts => by
      have hs : s = ∅ := h
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro w hw
      have : w ∈ s := hts hw
      simp [hs] at this
  | .conj φ ψ, h, hts => by
      exact ⟨supports_mono M h.1 hts, supports_mono M h.2 hts⟩
  | .inqDisj φ ψ, h, hts => by
      cases h with
      | inl hφ => exact Or.inl (supports_mono M hφ hts)
      | inr hψ => exact Or.inr (supports_mono M hψ hts)
  | .imp φ ψ, h, hts => by
      intro u hus hu
      exact h u (Subset.trans hus hts) hu
  | .forall_ x φ, h, hts => by
      intro d
      exact supports_mono M (h d) hts
  | .inqExists x φ, h, hts => by
      rcases h with ⟨d, hd⟩
      exact ⟨d, supports_mono M hd hts⟩

theorem supports_empty (M : InfoModel sig) (g : Assignment M.D) :
    ∀ φ : Formula sig, supports M (∅ : Set M.W) g φ
  | .pred _ _ => by
      intro w hw
      simp at hw
  | .eq _ _ => by
      intro w hw
      simp at hw
  | .bot => rfl
  | .conj φ ψ => by
      exact ⟨supports_empty M g φ, supports_empty M g ψ⟩
  | .inqDisj φ _ => by
      exact Or.inl (supports_empty M g φ)
  | .imp φ ψ => by
      intro t ht _
      have hte : t = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro w hw
        exact ht hw
      subst hte
      exact supports_empty M g ψ
  | .forall_ x φ => by
      intro d
      exact supports_empty M (Assignment.update g x d) φ
  | .inqExists x φ => by
      exact ⟨Classical.choice M.hD, supports_empty M (Assignment.update g x (Classical.choice M.hD)) φ⟩

end InqBQ
end HeytingLean
