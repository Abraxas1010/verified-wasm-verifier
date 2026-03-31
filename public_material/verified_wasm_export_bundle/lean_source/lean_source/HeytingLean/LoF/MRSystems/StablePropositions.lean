import HeytingLean.LoF.MRSystems.Truncation
import Mathlib.Order.Heyting.Basic

/-!
# (M,R) stable propositions — predicates on closed selectors

The Tier-1 (M,R) scaffold defines an idempotent “closure” endomap on selectors:

`closeSelector : Selector S → Selector S`

Its fixed points `IsClosed` are the “closed” selectors at a chosen configuration `b`.

This file extracts a clean *logic layer* from that data:

- **stable propositions** are predicates on the closed selectors,
  i.e. functions `ClosedSelectorFixed → Prop` (equivalently, sets);
- equivalently, they are the predicates `P : Selector S → Prop` whose truth value is
  invariant under closing: `P Φ ↔ P (closeSelector Φ)`.

This yields a Heyting algebra of stable propositions (in fact a Boolean algebra) because
`Set α` has pointwise Heyting operations.

This is intentionally modest: it does **not** attempt to manufacture a locale-theoretic nucleus
directly from `closeSelector` (which acts on *elements*, not on an ordered lattice).
-/

namespace HeytingLean
namespace LoF
namespace MRSystems

open HeytingLean.ClosingTheLoop.MR

universe u v

variable {S : MRSystem.{u, v}} {b : S.B} (RI : RightInverseAt S b)

/-! ## Closed selectors and stable propositions -/

/-- Closed selectors (fixed points of `closeSelector`). -/
abbrev ClosedSelectorFixed' : Type _ :=
  ClosedSelectorFixed (S := S) (b := b) RI

/-- Stable propositions: predicates on closed selectors. -/
abbrev StableProp : Type _ :=
  ClosedSelectorFixed' (S := S) (b := b) RI → Prop

instance : HeytingAlgebra (StableProp (S := S) (b := b) RI) := by
  infer_instance

/-! ## Stable predicates on all selectors -/

/-- A predicate on selectors is stable if it is invariant under `closeSelector`. -/
abbrev StablePred : Type _ :=
  {P : Selector S → Prop // ∀ Φ : Selector S, P Φ ↔ P (closeSelector S b RI Φ)}

/-- Package `closeSelector Φ` as a closed selector. -/
def closeAsClosed (Φ : Selector S) : ClosedSelectorFixed' (S := S) (b := b) RI :=
  ⟨closeSelector S b RI Φ, IsClosed.close_isClosed (S := S) (b := b) (RI := RI) Φ⟩

@[simp] theorem closeAsClosed_val (Φ : Selector S) :
    (closeAsClosed (S := S) (b := b) RI Φ : Selector S) = closeSelector S b RI Φ := rfl

@[simp] theorem closeAsClosed_close (Φ : Selector S) :
    closeAsClosed (S := S) (b := b) RI (closeSelector S b RI Φ) =
      closeAsClosed (S := S) (b := b) RI Φ := by
  apply Subtype.ext
  exact closeSelector.idem (S := S) (b := b) (RI := RI) Φ

/-! ## Equivalence: stable predicates ↔ predicates on closed selectors -/

namespace StablePred

/-- Restrict a stable predicate on all selectors to the closed ones. -/
def restrict :
    StablePred (S := S) (b := b) RI → StableProp (S := S) (b := b) RI :=
  fun P => fun Φc => P.1 Φc.1

/-- Extend a predicate on closed selectors to a stable predicate on all selectors by precomposing
with `closeSelector`. -/
def extend :
    StableProp (S := S) (b := b) RI → StablePred (S := S) (b := b) RI :=
  fun Q =>
    ⟨fun Φ => Q (closeAsClosed (S := S) (b := b) RI Φ), by
      intro Φ
      simp [closeAsClosed_close (S := S) (b := b) (RI := RI) Φ]⟩

@[simp] theorem restrict_extend (Q : StableProp (S := S) (b := b) RI) :
    restrict (S := S) (b := b) RI (extend (S := S) (b := b) RI Q) = Q := by
  funext Φc
  -- For a closed selector `Φc`, closing does nothing.
  have hΦ : closeSelector S b RI Φc.1 = Φc.1 := by
    exact Φc.2
  have : closeAsClosed (S := S) (b := b) RI Φc.1 = Φc := by
    apply Subtype.ext
    exact hΦ
  simp [restrict, extend, this]

@[simp] theorem extend_restrict (P : StablePred (S := S) (b := b) RI) :
    extend (S := S) (b := b) RI (restrict (S := S) (b := b) RI P) = P := by
  apply Subtype.ext
  funext Φ
  -- `extend (restrict P) Φ` = `P (close Φ)`, and stability gives `P Φ ↔ P (close Φ)`.
  apply propext
  simpa [extend, restrict, closeAsClosed] using (P.2 Φ).symm

/-- Stable predicates on selectors are equivalent to predicates on the closed selectors. -/
def equivStableProp :
    StablePred (S := S) (b := b) RI ≃ StableProp (S := S) (b := b) RI :=
  { toFun := restrict (S := S) (b := b) RI
    invFun := extend (S := S) (b := b) RI
    left_inv := by
      intro P
      simp
    right_inv := by
      intro Q
      simp }

end StablePred

end MRSystems
end LoF
end HeytingLean
