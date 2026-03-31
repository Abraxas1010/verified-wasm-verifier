import HeytingLean.Noneism.Semantics.RoutleyMeyer

/-!
# Noneism.ProofTheory.NDRM

Primary proof-theory surface for Routley-Meyer semantics.

Design choice in this sprint:
- `Derives` is defined as semantic consequence over `RM.Entails` (exact match to
  `Semantics/RoutleyMeyer.lean`).
- A labelled judgement layer is included so ternary-`R` and `star` obligations are explicit in the
  proof-theory API and can be refined into a fully syntactic ND/sequent presentation.
- No strengthening frame axioms are introduced.
-/

namespace HeytingLean
namespace Noneism
namespace NDRM

open Noneism Formula RM

abbrev Label := Nat
abbrev LabelValuation (W : Type) := Label → W

/-- Labelled judgement language for RM-style proof obligations. -/
inductive Judgment (σ : Type) where
  | frm  : Label → Formula σ → Judgment σ
  | rel  : Label → Label → Label → Judgment σ
  | star : Label → Label → Judgment σ
  deriving DecidableEq, Repr

/-- Semantic realization of labelled judgements. -/
def Realizes {σ W D : Type}
    (M : RM.Model σ W D) (ρ : RM.Valuation D) (η : LabelValuation W) :
    Judgment σ → Prop
  | .frm l φ    => RM.sat M ρ (η l) φ
  | .rel l u v  => M.F.R (η l) (η u) (η v)
  | .star l u   => η u = M.F.star (η l)

/-- Labelled semantic entailment. -/
def EntailsL {σ : Type} (Γ : List (Judgment σ)) (j : Judgment σ) : Prop :=
  ∀ (W D : Type) (M : RM.Model σ W D) (ρ : RM.Valuation D) (η : LabelValuation W),
    (∀ a ∈ Γ, Realizes M ρ η a) → Realizes M ρ η j

/--
Semantic derivability surface for labelled RM judgements.

This keeps a stable API while ND/sequent syntactic presentations are iterated in parallel.
-/
abbrev DerivesL {σ : Type} (Γ : List (Judgment σ)) (j : Judgment σ) : Prop := EntailsL Γ j

/-- Embed an ordinary formula context at the distinguished label `0`. -/
def embedAtZero {σ : Type} (Γ : List (Formula σ)) : List (Judgment σ) :=
  Γ.map (fun φ => Judgment.frm 0 φ)

/-- Unlabelled derivability: formula consequence at distinguished label `0`. -/
def Derives {σ : Type} (Γ : List (Formula σ)) (φ : Formula σ) : Prop :=
  DerivesL (embedAtZero Γ) (Judgment.frm 0 φ)

theorem derives_iff_entails {σ : Type} {Γ : List (Formula σ)} {φ : Formula σ} :
    Derives Γ φ ↔ RM.Entails Γ φ := by
  constructor
  · intro h
    intro W D M ρ w hΓ
    let η : LabelValuation W := fun _ => w
    have hEmb : ∀ a ∈ embedAtZero Γ, Realizes M ρ η a := by
      intro a ha
      rcases List.mem_map.1 ha with ⟨ψ, hψ, rfl⟩
      simpa [embedAtZero, Realizes, η] using hΓ ψ hψ
    simpa [Derives, DerivesL, EntailsL, Realizes, η] using h W D M ρ η hEmb
  · intro h
    intro W D M ρ η hEmb
    have hΓ : ∀ ψ ∈ Γ, RM.sat M ρ (η 0) ψ := by
      intro ψ hψ
      have hmem : Judgment.frm 0 ψ ∈ embedAtZero Γ := by
        exact List.mem_map.2 ⟨ψ, hψ, rfl⟩
      simpa [Realizes] using hEmb (Judgment.frm 0 ψ) hmem
    simpa [Derives, DerivesL, EntailsL, Realizes] using h W D M ρ (η 0) hΓ

theorem derives_eq_entails {σ : Type} (Γ : List (Formula σ)) (φ : Formula σ) :
    Derives Γ φ = RM.Entails Γ φ :=
  propext (derives_iff_entails (Γ := Γ) (φ := φ))

end NDRM
end Noneism
end HeytingLean
