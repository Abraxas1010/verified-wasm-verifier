import HeytingLean.Noneism.ProofTheory.ND

/-!
# Noneism.ProofTheory.Quantifiers.DerivesScoped

Scoped derivations for quantifier metatheory.

`DerivesScoped E Γ φ` tracks an explicit finite scope `E` of variables that the ambient
assumption context is allowed to mention (`fvContext Γ ⊆ E`). Quantifier-introduction/elimination
rules then use freshness side conditions against `E`.

This provides a first step toward replacing post-hoc freshness extraction with an explicit
proof-state discipline.
-/

namespace HeytingLean
namespace Noneism

open Formula

namespace ND

variable {σ : Type}

/--
Scoped derivations.

`E` is an explicit finite scope for free variables in the ambient context.
-/
inductive DerivesScoped : Finset Var → List (Formula σ) → Formula σ → Prop
  | hyp {E : Finset Var} {Γ : List (Formula σ)} {φ : Formula σ}
      (hCtx : ND.fvContext (σ := σ) Γ ⊆ E)
      (hMem : φ ∈ Γ) :
      DerivesScoped E Γ φ
  | topI {E : Finset Var} {Γ : List (Formula σ)}
      (hCtx : ND.fvContext (σ := σ) Γ ⊆ E) :
      DerivesScoped E Γ .top
  | botE {E : Finset Var} {Γ : List (Formula σ)} {φ : Formula σ}
      (h : DerivesScoped E Γ .bot) :
      DerivesScoped E Γ φ
  | andI {E : Finset Var} {Γ : List (Formula σ)} {φ ψ : Formula σ}
      (h1 : DerivesScoped E Γ φ)
      (h2 : DerivesScoped E Γ ψ) :
      DerivesScoped E Γ (.and φ ψ)
  | andEL {E : Finset Var} {Γ : List (Formula σ)} {φ ψ : Formula σ}
      (h : DerivesScoped E Γ (.and φ ψ)) :
      DerivesScoped E Γ φ
  | andER {E : Finset Var} {Γ : List (Formula σ)} {φ ψ : Formula σ}
      (h : DerivesScoped E Γ (.and φ ψ)) :
      DerivesScoped E Γ ψ
  | orIL {E : Finset Var} {Γ : List (Formula σ)} {φ ψ : Formula σ}
      (h : DerivesScoped E Γ φ) :
      DerivesScoped E Γ (.or φ ψ)
  | orIR {E : Finset Var} {Γ : List (Formula σ)} {φ ψ : Formula σ}
      (h : DerivesScoped E Γ ψ) :
      DerivesScoped E Γ (.or φ ψ)
  | orE {E : Finset Var} {Γ : List (Formula σ)} {φ ψ χ : Formula σ}
      (hCtx : ND.fvContext (σ := σ) Γ ⊆ E)
      (hOr : DerivesScoped E Γ (.or φ ψ))
      (hL : DerivesScoped (E ∪ Syntax.fvFormula (σ := σ) φ) (φ :: Γ) χ)
      (hR : DerivesScoped (E ∪ Syntax.fvFormula (σ := σ) ψ) (ψ :: Γ) χ) :
      DerivesScoped E Γ χ
  | impI {E : Finset Var} {Γ : List (Formula σ)} {φ ψ : Formula σ}
      (hCtx : ND.fvContext (σ := σ) Γ ⊆ E)
      (h : DerivesScoped (E ∪ Syntax.fvFormula (σ := σ) φ) (φ :: Γ) ψ) :
      DerivesScoped E Γ (.imp φ ψ)
  | impE {E : Finset Var} {Γ : List (Formula σ)} {φ ψ : Formula σ}
      (h1 : DerivesScoped E Γ (.imp φ ψ))
      (h2 : DerivesScoped E Γ φ) :
      DerivesScoped E Γ ψ
  | notI {E : Finset Var} {Γ : List (Formula σ)} {φ : Formula σ}
      (hCtx : ND.fvContext (σ := σ) Γ ⊆ E)
      (h : DerivesScoped (E ∪ Syntax.fvFormula (σ := σ) φ) (φ :: Γ) .bot) :
      DerivesScoped E Γ (.not φ)
  | notE {E : Finset Var} {Γ : List (Formula σ)} {φ : Formula σ}
      (h1 : DerivesScoped E Γ (.not φ))
      (h2 : DerivesScoped E Γ φ) :
      DerivesScoped E Γ .bot
  | piI {E : Finset Var} {Γ : List (Formula σ)} {x a : Var} {φ : Formula σ}
      (hCtx : ND.fvContext (σ := σ) Γ ⊆ E)
      (haE : a ∉ E)
      (haVars : a ∉ Syntax.varsFormula (σ := σ) φ)
      (h : DerivesScoped E Γ (Syntax.substFormula (σ := σ) x (.var a) φ)) :
      DerivesScoped E Γ (.pi x φ)
  | piE {E : Finset Var} {Γ : List (Formula σ)} {x a : Var} {φ : Formula σ}
      (h : DerivesScoped E Γ (.pi x φ)) :
      DerivesScoped E Γ (Syntax.substFormula (σ := σ) x (.var a) φ)
  | sigmaI {E : Finset Var} {Γ : List (Formula σ)} {x a : Var} {φ : Formula σ}
      (h : DerivesScoped E Γ (Syntax.substFormula (σ := σ) x (.var a) φ)) :
      DerivesScoped E Γ (.sigma x φ)
  | sigmaE {E : Finset Var} {Γ : List (Formula σ)} {x a : Var} {φ χ : Formula σ}
      (hCtx : ND.fvContext (σ := σ) Γ ⊆ E)
      (hSigma : DerivesScoped E Γ (.sigma x φ))
      (haE : a ∉ E)
      (haVars : a ∉ Syntax.varsFormula (σ := σ) φ)
      (haχ : a ∉ Syntax.fvFormula (σ := σ) χ)
      (hDer :
        DerivesScoped
          (E ∪ Syntax.fvFormula (σ := σ) (Syntax.substFormula (σ := σ) x (.var a) φ))
          (Syntax.substFormula (σ := σ) x (.var a) φ :: Γ) χ) :
      DerivesScoped E Γ χ
  | wk {E E' : Finset Var} {Γ Δ : List (Formula σ)} {φ : Formula σ}
      (hCtx : ND.fvContext (σ := σ) Δ ⊆ E')
      (h : DerivesScoped E Γ φ)
      (hSub : Γ ⊆ Δ)
      (hScope : E ⊆ E') :
      DerivesScoped E' Δ φ

namespace DerivesScoped

theorem context_subset_scope {E : Finset Var} {Γ : List (Formula σ)} {φ : Formula σ} :
    DerivesScoped E Γ φ → ND.fvContext (σ := σ) Γ ⊆ E := by
  intro h
  induction h with
  | hyp hCtx _ =>
      exact hCtx
  | topI hCtx =>
      exact hCtx
  | botE _ ih =>
      exact ih
  | andI _ _ ih _ =>
      exact ih
  | andEL _ ih =>
      exact ih
  | andER _ ih =>
      exact ih
  | orIL _ ih =>
      exact ih
  | orIR _ ih =>
      exact ih
  | orE hCtx _ _ _ =>
      exact hCtx
  | impI hCtx _ =>
      exact hCtx
  | impE _ _ ih _ =>
      exact ih
  | notI hCtx _ =>
      exact hCtx
  | notE _ _ ih _ =>
      exact ih
  | piI hCtx _ _ _ =>
      exact hCtx
  | piE _ ih =>
      exact ih
  | sigmaI _ ih =>
      exact ih
  | sigmaE hCtx _ _ _ _ _ =>
      exact hCtx
  | wk hCtx _ _ _ =>
      exact hCtx

/-- Forget scope bookkeeping and recover an ordinary ND derivation. -/
theorem toDerives {E : Finset Var} {Γ : List (Formula σ)} {φ : Formula σ} :
    DerivesScoped E Γ φ → Derives (σ := σ) Γ φ := by
  intro h
  induction h with
  | hyp _ hMem =>
      exact Derives.hyp hMem
  | topI _ =>
      exact Derives.topI
  | botE h ih =>
      exact Derives.botE ih
  | andI _ _ ih1 ih2 =>
      exact Derives.andI ih1 ih2
  | andEL _ ih =>
      exact Derives.andEL ih
  | andER _ ih =>
      exact Derives.andER ih
  | orIL _ ih =>
      exact Derives.orIL ih
  | orIR _ ih =>
      exact Derives.orIR ih
  | orE _ _ _ _ ihOr ihL ihR =>
      exact Derives.orE ihOr ihL ihR
  | impI _ _ ih =>
      exact Derives.impI ih
  | impE _ _ ih1 ih2 =>
      exact Derives.impE ih1 ih2
  | notI _ _ ih =>
      exact Derives.notI ih
  | notE _ _ ih1 ih2 =>
      exact Derives.notE ih1 ih2
  | piI hCtx haE haVars h ih =>
      exact Derives.piI
        (by
          intro haΓ
          exact haE (hCtx haΓ))
        haVars
        ih
  | piE _ ih =>
      exact Derives.piE ih
  | sigmaI _ ih =>
      exact Derives.sigmaI ih
  | sigmaE hCtx hSigma haE haVars haχ hDer ihSigma ihDer =>
      exact Derives.sigmaE
        ihSigma
        (by
          intro haΓ
          exact haE (hCtx haΓ))
        haVars
        haχ
        ihDer
  | wk _ _ hSub _ ih =>
      exact Derives.wk ih hSub

/--
Embed ordinary derivations into scoped derivations using `E = fvContext Γ`.
-/
theorem ofDerives {Γ : List (Formula σ)} {φ : Formula σ} :
    Derives (σ := σ) Γ φ →
      DerivesScoped (ND.fvContext (σ := σ) Γ) Γ φ := by
  intro h
  induction h with
  | hyp hMem =>
      exact DerivesScoped.hyp (hCtx := by intro x hx; exact hx) hMem
  | topI =>
      exact DerivesScoped.topI (hCtx := by intro x hx; exact hx)
  | botE h ih =>
      exact DerivesScoped.botE ih
  | andI h1 h2 ih1 ih2 =>
      exact DerivesScoped.andI ih1 ih2
  | andEL h ih =>
      exact DerivesScoped.andEL ih
  | andER h ih =>
      exact DerivesScoped.andER ih
  | orIL h ih =>
      exact DerivesScoped.orIL ih
  | orIR h ih =>
      exact DerivesScoped.orIR ih
  | orE hOr hL hR ihOr ihL ihR =>
      rename_i Γ φ ψ χ
      have ihL' :
          DerivesScoped
            (ND.fvContext (σ := σ) Γ ∪ Syntax.fvFormula (σ := σ) φ)
            (φ :: Γ) χ := by
        simpa [ND.fvContext, Finset.union_assoc, Finset.union_comm, Finset.union_left_comm]
          using ihL
      have ihR' :
          DerivesScoped
            (ND.fvContext (σ := σ) Γ ∪ Syntax.fvFormula (σ := σ) ψ)
            (ψ :: Γ) χ := by
        simpa [ND.fvContext, Finset.union_assoc, Finset.union_comm, Finset.union_left_comm]
          using ihR
      exact DerivesScoped.orE (hCtx := by intro x hx; exact hx) ihOr ihL' ihR'
  | impI h ih =>
      rename_i Γ φ ψ
      have ih' :
          DerivesScoped
            (ND.fvContext (σ := σ) Γ ∪ Syntax.fvFormula (σ := σ) φ)
            (φ :: Γ) ψ := by
        simpa [ND.fvContext, Finset.union_assoc, Finset.union_comm, Finset.union_left_comm]
          using ih
      exact DerivesScoped.impI (hCtx := by intro x hx; exact hx) ih'
  | impE h1 h2 ih1 ih2 =>
      exact DerivesScoped.impE ih1 ih2
  | notI h ih =>
      rename_i Γ φ
      have ih' :
          DerivesScoped
            (ND.fvContext (σ := σ) Γ ∪ Syntax.fvFormula (σ := σ) φ)
            (φ :: Γ) .bot := by
        simpa [ND.fvContext, Finset.union_assoc, Finset.union_comm, Finset.union_left_comm]
          using ih
      exact DerivesScoped.notI (hCtx := by intro x hx; exact hx) ih'
  | notE h1 h2 ih1 ih2 =>
      exact DerivesScoped.notE ih1 ih2
  | piI haΓ haVars h ih =>
      rename_i Γ x a φ
      exact DerivesScoped.piI
        (hCtx := by intro x hx; exact hx)
        (a := a)
        (x := x)
        (φ := φ)
        (by simpa using haΓ)
        haVars
        ih
  | piE h ih =>
      exact DerivesScoped.piE ih
  | sigmaI h ih =>
      exact DerivesScoped.sigmaI ih
  | sigmaE hSigma haΓ haVars haχ hDer ihSigma ihDer =>
      rename_i Γ x a φ χ
      let θ : Formula σ := Syntax.substFormula (σ := σ) x (.var a) φ
      have ihDer' :
          DerivesScoped
            (ND.fvContext (σ := σ) Γ ∪ Syntax.fvFormula (σ := σ) θ)
            (θ :: Γ) χ := by
        simpa [θ, ND.fvContext, Finset.union_assoc, Finset.union_comm, Finset.union_left_comm]
          using ihDer
      exact DerivesScoped.sigmaE
        (hCtx := by intro x hx; exact hx)
        (x := x)
        (a := a)
        (φ := φ)
        (χ := χ)
        ihSigma
        (by simpa using haΓ)
        haVars
        haχ
        ihDer'
  | wk h hSub ih =>
      exact DerivesScoped.wk
        (hCtx := by
          intro x hx
          exact hx)
        ih
        hSub
        (ND.fvContext_mono (σ := σ) hSub)

end DerivesScoped

end ND

end Noneism
end HeytingLean
