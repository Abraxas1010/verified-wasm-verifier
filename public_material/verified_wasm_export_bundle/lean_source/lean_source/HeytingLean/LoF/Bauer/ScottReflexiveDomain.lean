import Mathlib.Order.OmegaCompletePartialOrder

/-!
# Scott-style reflexive domains and fixed points

This module adds a small, explicit *Scott-style* interface for a **reflexive domain**,
and a fixed-point theorem for Scott-continuous endomaps.

We reuse Mathlib’s ωCPO + Scott-continuous map infrastructure:

* `OmegaCompletePartialOrder α`
* continuous maps `α →𝒄 β` (bundled monotone maps preserving `ωSup` of chains)
* the fixed-point lemma `OmegaCompletePartialOrder.fixedPoints.ωSup_iterate_mem_fixedPoint`.

The intent is to provide the “reflexive domain + Y combinator” layer needed for the
generative `LoF → eigenforms → combinators → type theory` narrative, without introducing
global axioms or placeholder proofs.
-/

namespace HeytingLean
namespace LoF
namespace Bauer

open OmegaCompletePartialOrder

universe u

section FixedPoints

variable {α : Type u} [OmegaCompletePartialOrder α] [OrderBot α]

/-- A Scott-style fixed-point operator (Kleene iteration from `⊥`). -/
noncomputable def scottFix (f : α →𝒄 α) : α :=
  ωSup (OmegaCompletePartialOrder.fixedPoints.iterateChain f ⊥ bot_le)

theorem scottFix_isFixed (f : α →𝒄 α) : f (scottFix (α := α) f) = scottFix (α := α) f := by
  -- `ωSup_iterate_mem_fixedPoint` gives membership in `Function.fixedPoints`.
  have hmem :
      scottFix (α := α) f ∈ Function.fixedPoints f := by
    simpa [scottFix] using
      (OmegaCompletePartialOrder.fixedPoints.ωSup_iterate_mem_fixedPoint (f := f) (x := (⊥ : α))
        (h := (bot_le : (⊥ : α) ≤ f (⊥ : α))))
  simpa [Function.mem_fixedPoints] using (hmem : f (scottFix (α := α) f) = scottFix (α := α) f)

end FixedPoints

/-! ## Scott-style reflexive domains -/

section Reflexive

variable {α : Type u} [OmegaCompletePartialOrder α] [OrderBot α]

/-- A **Scott-style reflexive domain**: an ωCPO with bottom that is (explicitly) equivalent
to its space of Scott-continuous endomaps.

This is the usual untyped-lambda-calculus “reflexive object” requirement, but phrased
as an explicit equivalence in the category of ωCPOs + Scott-continuous maps.
-/
structure ReflexiveDomain (α : Type u) [OmegaCompletePartialOrder α] [OrderBot α] where
  equivEndo : α ≃ (α →𝒄 α)

namespace ReflexiveDomain

/-- Application induced by the reflexivity equivalence. -/
def app (D : ReflexiveDomain (α := α)) (d x : α) : α :=
  (D.equivEndo d) x

/-- A canonical “Y operator” on continuous endomaps, defined via Scott/Kleene iteration. -/
noncomputable def Y (_D : ReflexiveDomain (α := α)) (f : α →𝒄 α) : α :=
  scottFix (α := α) f

theorem Y_isFixed (D : ReflexiveDomain (α := α)) (f : α →𝒄 α) :
    f (Y (α := α) D f) = Y (α := α) D f :=
  scottFix_isFixed (α := α) f

end ReflexiveDomain

end Reflexive

end Bauer
end LoF
end HeytingLean
