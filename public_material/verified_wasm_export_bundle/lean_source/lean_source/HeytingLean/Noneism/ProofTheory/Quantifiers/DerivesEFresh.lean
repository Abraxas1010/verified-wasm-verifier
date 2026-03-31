import HeytingLean.Noneism.ProofTheory.ND

/-!
# Noneism.ProofTheory.Quantifiers.DerivesEFresh

An explicit freshness-tracked derivation layer for FO quantifier work.

`DerivesEFresh u Γ φ` means we have a derivation of `φ` from `Γ` while explicitly tracking that
`u` is fresh for the ambient context (`u ∉ ND.fvContext Γ`) at each judgment node.

This gives a stable proof target for completeness work that currently gets stuck on post-hoc
freshness extraction from arbitrary finite derivation contexts.
-/

namespace HeytingLean
namespace Noneism

open Formula

namespace ND

variable {σ : Type}

/--
Freshness-tracked derivations.

`u` is the tracked variable we require to stay fresh in every judgment context.
-/
inductive DerivesEFresh (u : Var) : List (Formula σ) → Formula σ → Prop
  | hyp {Γ : List (Formula σ)} {φ : Formula σ} :
      u ∉ ND.fvContext (σ := σ) Γ →
      φ ∈ Γ →
      DerivesEFresh u Γ φ
  | topI {Γ : List (Formula σ)} :
      u ∉ ND.fvContext (σ := σ) Γ →
      DerivesEFresh u Γ .top
  | botE {Γ : List (Formula σ)} {φ : Formula σ} :
      DerivesEFresh u Γ .bot →
      DerivesEFresh u Γ φ
  | andI {Γ : List (Formula σ)} {φ ψ : Formula σ} :
      DerivesEFresh u Γ φ →
      DerivesEFresh u Γ ψ →
      DerivesEFresh u Γ (.and φ ψ)
  | andEL {Γ : List (Formula σ)} {φ ψ : Formula σ} :
      DerivesEFresh u Γ (.and φ ψ) →
      DerivesEFresh u Γ φ
  | andER {Γ : List (Formula σ)} {φ ψ : Formula σ} :
      DerivesEFresh u Γ (.and φ ψ) →
      DerivesEFresh u Γ ψ
  | orIL {Γ : List (Formula σ)} {φ ψ : Formula σ} :
      DerivesEFresh u Γ φ →
      DerivesEFresh u Γ (.or φ ψ)
  | orIR {Γ : List (Formula σ)} {φ ψ : Formula σ} :
      DerivesEFresh u Γ ψ →
      DerivesEFresh u Γ (.or φ ψ)
  | orE {Γ : List (Formula σ)} {φ ψ χ : Formula σ} :
      DerivesEFresh u Γ (.or φ ψ) →
      DerivesEFresh u (φ :: Γ) χ →
      DerivesEFresh u (ψ :: Γ) χ →
      DerivesEFresh u Γ χ
  | impI {Γ : List (Formula σ)} {φ ψ : Formula σ} :
      DerivesEFresh u (φ :: Γ) ψ →
      DerivesEFresh u Γ (.imp φ ψ)
  | impE {Γ : List (Formula σ)} {φ ψ : Formula σ} :
      DerivesEFresh u Γ (.imp φ ψ) →
      DerivesEFresh u Γ φ →
      DerivesEFresh u Γ ψ
  | notI {Γ : List (Formula σ)} {φ : Formula σ} :
      DerivesEFresh u (φ :: Γ) .bot →
      DerivesEFresh u Γ (.not φ)
  | notE {Γ : List (Formula σ)} {φ : Formula σ} :
      DerivesEFresh u Γ (.not φ) →
      DerivesEFresh u Γ φ →
      DerivesEFresh u Γ .bot
  | piI {Γ : List (Formula σ)} {x a : Var} {φ : Formula σ} :
      a ∉ ND.fvContext (σ := σ) Γ →
      a ∉ Syntax.varsFormula (σ := σ) φ →
      DerivesEFresh u Γ (Syntax.substFormula (σ := σ) x (.var a) φ) →
      DerivesEFresh u Γ (.pi x φ)
  | piE {Γ : List (Formula σ)} {x a : Var} {φ : Formula σ} :
      DerivesEFresh u Γ (.pi x φ) →
      DerivesEFresh u Γ (Syntax.substFormula (σ := σ) x (.var a) φ)
  | sigmaI {Γ : List (Formula σ)} {x a : Var} {φ : Formula σ} :
      DerivesEFresh u Γ (Syntax.substFormula (σ := σ) x (.var a) φ) →
      DerivesEFresh u Γ (.sigma x φ)
  | sigmaE {Γ : List (Formula σ)} {x a : Var} {φ χ : Formula σ} :
      DerivesEFresh u Γ (.sigma x φ) →
      a ∉ ND.fvContext (σ := σ) Γ →
      a ∉ Syntax.varsFormula (σ := σ) φ →
      a ∉ Syntax.fvFormula (σ := σ) χ →
      DerivesEFresh u (Syntax.substFormula (σ := σ) x (.var a) φ :: Γ) χ →
      DerivesEFresh u Γ χ
  | fromDerives {Γ : List (Formula σ)} {φ : Formula σ} :
      u ∉ ND.fvContext (σ := σ) Γ →
      Derives (σ := σ) Γ φ →
      DerivesEFresh u Γ φ
  | wk {Γ Δ : List (Formula σ)} {φ : Formula σ} :
      DerivesEFresh u Γ φ →
      Γ ⊆ Δ →
      u ∉ ND.fvContext (σ := σ) Δ →
      DerivesEFresh u Δ φ

namespace DerivesEFresh

theorem fresh_context {u : Var} {Γ : List (Formula σ)} {φ : Formula σ} :
    DerivesEFresh (σ := σ) u Γ φ -> u ∉ ND.fvContext (σ := σ) Γ := by
  intro h
  induction h with
  | hyp hFresh _ =>
      exact hFresh
  | topI hFresh =>
      exact hFresh
  | botE h ih =>
      exact ih
  | andI h1 h2 ih1 _ =>
      exact ih1
  | andEL h ih =>
      exact ih
  | andER h ih =>
      exact ih
  | orIL h ih =>
      exact ih
  | orIR h ih =>
      exact ih
  | orE hOr _ _ ihOr _ _ =>
      exact ihOr
  | impI h ih =>
      rename_i Γ φ ψ
      have hsplit : u ∉ Syntax.fvFormula (σ := σ) φ ∧ u ∉ ND.fvContext (σ := σ) Γ := by
        have : u ∉ Syntax.fvFormula (σ := σ) φ ∪ ND.fvContext (σ := σ) Γ := by
          simpa [ND.fvContext] using ih
        simpa [Finset.mem_union] using this
      exact hsplit.2
  | impE h1 h2 ih1 _ =>
      exact ih1
  | notI h ih =>
      rename_i Γ φ
      have hsplit : u ∉ Syntax.fvFormula (σ := σ) φ ∧ u ∉ ND.fvContext (σ := σ) Γ := by
        have : u ∉ Syntax.fvFormula (σ := σ) φ ∪ ND.fvContext (σ := σ) Γ := by
          simpa [ND.fvContext] using ih
        simpa [Finset.mem_union] using this
      exact hsplit.2
  | notE h1 h2 ih1 _ =>
      exact ih1
  | piI _ _ h ih =>
      exact ih
  | piE h ih =>
      exact ih
  | sigmaI h ih =>
      exact ih
  | sigmaE hSigma _ _ _ hDer ihSigma _ =>
      exact ihSigma
  | fromDerives hFresh _ =>
      exact hFresh
  | wk _ _ hFresh =>
      exact hFresh

/-- Forget freshness bookkeeping and recover a standard ND derivation. -/
theorem toDerives {u : Var} {Γ : List (Formula σ)} {φ : Formula σ} :
    DerivesEFresh (σ := σ) u Γ φ -> Derives (σ := σ) Γ φ := by
  intro h
  induction h with
  | hyp _ hMem =>
      exact Derives.hyp hMem
  | topI _ =>
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
  | orE hOr hL hR ihOr ihL ihR =>
      exact Derives.orE ihOr ihL ihR
  | impI h ih =>
      exact Derives.impI ih
  | impE h1 h2 ih1 ih2 =>
      exact Derives.impE ih1 ih2
  | notI h ih =>
      exact Derives.notI ih
  | notE h1 h2 ih1 ih2 =>
      exact Derives.notE ih1 ih2
  | piI haΓ haVars h ih =>
      exact Derives.piI haΓ haVars ih
  | piE h ih =>
      exact Derives.piE ih
  | sigmaI h ih =>
      exact Derives.sigmaI ih
  | sigmaE hSigma haΓ haVars haχ hDer ihSigma ihDer =>
      exact Derives.sigmaE ihSigma haΓ haVars haχ ihDer
  | fromDerives _ hDer =>
      exact hDer
  | wk h hSub _ ih =>
      exact Derives.wk ih hSub

theorem weaken {u : Var} {Γ Δ : List (Formula σ)} {φ : Formula σ}
    (h : DerivesEFresh (σ := σ) u Γ φ)
    (hSub : Γ ⊆ Δ)
    (hFreshΔ : u ∉ ND.fvContext (σ := σ) Δ) :
    DerivesEFresh (σ := σ) u Δ φ :=
  DerivesEFresh.wk h hSub hFreshΔ

/--
Lift an ordinary ND derivation into freshness-tracked derivations whenever `u` is fresh for the
ambient context.
-/
theorem ofDerives {u : Var} {Γ : List (Formula σ)} {φ : Formula σ}
    (hFreshΓ : u ∉ ND.fvContext (σ := σ) Γ) :
    Derives (σ := σ) Γ φ -> DerivesEFresh (σ := σ) u Γ φ := by
  intro hDer
  exact DerivesEFresh.fromDerives hFreshΓ hDer

end DerivesEFresh

end ND

end Noneism
end HeytingLean
