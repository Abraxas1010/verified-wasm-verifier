import Mathlib.Order.Nucleus
import Mathlib.Data.Set.BooleanAlgebra

/-!
# Commitment via a nucleus on `Set PreGame`

This module formalizes the order-theoretic commitment map induced by a
nucleus `R : Nucleus (Set PreGame)`. A witness `w : W` is encoded as a
set of pre-games `encode w : Set PreGame`, and we publish the fixed-point
`R (encode w)` as an element of `Ω := R.toSublocale`.

There are no cryptographic claims here; everything is purely algebraic.
-/

namespace HeytingLean
namespace Crypto
namespace Commit

variable {PreGame : Type*}

/-! ## Witness encoding -/

/-- A witness space `W` with an encoding into `Set PreGame`. -/
structure EncodableWitness (PreGame : Type*) where
  W      : Type*
  encode : W → Set PreGame

/-- Bundle a nucleus on `Set PreGame` with its fixed-point type `Ω`. -/
structure NucleusCtx (PreGame : Type*) where
  R  : Nucleus (Set PreGame)

namespace NucleusCtx

variable (NC : NucleusCtx PreGame)

abbrev Ω := {x : Set PreGame // NC.R x = x}

/-! ## Commitment map and its basic properties -/

/-- The canonical commitment induced by the nucleus and the encoding. -/
def commit (EW : EncodableWitness PreGame) : EW.W → Ω (NC := NC) :=
  fun w =>
    let S := EW.encode w
    -- fixed-point certificate via nucleus idempotence
    ⟨NC.R S, NC.R.idempotent S⟩

/-- Preimage set of a committed public Ω-element. -/
def preimage (EW : EncodableWitness PreGame) (y : Ω (NC := NC)) : Set EW.W :=
  { w | ((commit (NC := NC) EW w : Set PreGame) = (Subtype.val y)) }

/-- Two witnesses are R-equivalent if their commitments coincide. -/
def equivR (EW : EncodableWitness PreGame) : EW.W → EW.W → Prop :=
  fun w₁ w₂ =>
    ((commit (NC := NC) EW w₁ : Set PreGame) = (commit (NC := NC) EW w₂ : Set PreGame))

theorem equivR_refl (EW : EncodableWitness PreGame) : Reflexive (equivR (NC := NC) EW) := by
  intro w; rfl

theorem equivR_symm (EW : EncodableWitness PreGame) : Symmetric (equivR (NC := NC) EW) := by
  intro w₁ w₂ h; simpa [equivR] using h.symm

theorem equivR_trans (EW : EncodableWitness PreGame) : Transitive (equivR (NC := NC) EW) := by
  intro a b c h₁ h₂; simpa [equivR] using h₁.trans h₂

/-- Quotient of witnesses by the commitment equivalence. -/
def QuotR (EW : EncodableWitness PreGame) := Quot (equivR (NC := NC) EW)

/-- Public statement carrier (fixed points of the nucleus). -/
@[simp] def stmt (_EW : EncodableWitness PreGame) := Ω (NC := NC)

/-- Universal map from the witness quotient to public statements. -/
def quotToStmt (EW : EncodableWitness PreGame) : QuotR (NC := NC) EW → stmt (NC := NC) EW :=
  Quot.lift (fun w => commit (NC := NC) EW w) (by
    intro a b h
    -- equality in Ω is definitional equality of underlying sets
    apply Subtype.ext
    simpa [equivR] using h)

/-- Verification relation: `(w, y)` is valid iff `y = commit w`. -/
def Rel (EW : EncodableWitness PreGame) (w : EW.W) (y : stmt (NC := NC) EW) : Prop :=
  ((commit (NC := NC) EW w : Set PreGame) = (Subtype.val y))

/-- Functionality of `Rel` in the public output for a fixed witness. -/
theorem Rel_functional (EW : EncodableWitness PreGame) (w : EW.W) :
    ∀ {y₁ y₂ : stmt (NC := NC) EW},
      Rel (NC := NC) EW w y₁ → Rel (NC := NC) EW w y₂ → y₁ = y₂ := by
  intro y₁ y₂ h1 h2
  apply Subtype.ext
  exact h1.symm.trans h2

end NucleusCtx

end Commit
end Crypto
end HeytingLean
