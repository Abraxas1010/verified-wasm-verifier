import HeytingLean.ClosingTheLoop.MR.ClosureOperator

/-!
# (M,R) “truncation” — quotienting selectors by `closeSelector`

This file mirrors `LoF/Combinators/Topos/Truncation.lean`, but for the Tier-1
Rosen-style selector closure operator:

* define an equivalence relation `Φ ~ Ψ` iff `closeSelector Φ = closeSelector Ψ`;
* show the quotient is equivalent to the type of `closeSelector`-closed selectors.

This is a *kernel quotient of an idempotent endomorphism*, not HoTT truncation.
-/

namespace HeytingLean
namespace LoF
namespace MRSystems

open Classical

open HeytingLean.ClosingTheLoop.MR

universe u v

variable {S : MRSystem.{u, v}} {b : S.B} (RI : RightInverseAt S b)

section

/-- The setoid identifying selectors with the same `closeSelector` image. -/
def closeSetoid : Setoid (Selector S) where
  r := fun Φ Ψ => closeSelector S b RI Φ = closeSelector S b RI Ψ
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro Φ
      rfl
    · intro Φ Ψ h
      exact h.symm
    · intro Φ Ψ Χ h₁ h₂
      exact h₁.trans h₂

abbrev CloseQuot : Type _ :=
  Quot (closeSetoid (S := S) (b := b) RI)

/-- Closed selectors, packaged as the range of `closeSelector`. -/
abbrev ClosedSelector : Type _ :=
  {Φ : Selector S // ∃ Ψ : Selector S, closeSelector S b RI Ψ = Φ}

noncomputable def quotToClosed : CloseQuot (S := S) (b := b) RI → ClosedSelector (S := S) (b := b) RI :=
  Quot.lift (fun Φ => ⟨closeSelector S b RI Φ, ⟨Φ, rfl⟩⟩) (by
    intro Φ Ψ h
    apply Subtype.ext
    simpa using h)

noncomputable def closedToQuot : ClosedSelector (S := S) (b := b) RI → CloseQuot (S := S) (b := b) RI :=
  fun T => Quot.mk _ T.1

noncomputable def closeQuotEquivClosed :
    CloseQuot (S := S) (b := b) RI ≃ ClosedSelector (S := S) (b := b) RI := by
  classical
  refine
    { toFun := quotToClosed (S := S) (b := b) RI
      invFun := closedToQuot (S := S) (b := b) RI
      left_inv := ?_
      right_inv := ?_ }
  · intro q
    refine Quot.inductionOn q ?_
    intro Φ
    apply Quot.sound
    change closeSelector S b RI (closeSelector S b RI Φ) = closeSelector S b RI Φ
    simpa using (closeSelector.idem (S := S) (b := b) (RI := RI) Φ)
  · intro T
    apply Subtype.ext
    rcases T.2 with ⟨Ψ, hΨ⟩
    -- `T` is in the range, hence fixed by idempotence.
    calc
      closeSelector S b RI T.1 = closeSelector S b RI (closeSelector S b RI Ψ) := by
        simp [hΨ.symm]
      _ = closeSelector S b RI Ψ := by
        simpa using (closeSelector.idem (S := S) (b := b) (RI := RI) Ψ)
      _ = T.1 := hΨ

/-! ## Range vs. fixed points -/

/-- Closed selectors as fixed points of `closeSelector`. -/
abbrev ClosedSelectorFixed : Type _ :=
  {Φ : Selector S // IsClosed S b RI Φ}

noncomputable def rangeToFixed :
    ClosedSelector (S := S) (b := b) RI → ClosedSelectorFixed (S := S) (b := b) RI := by
  intro T
  refine ⟨T.1, ?_⟩
  rcases T.2 with ⟨Ψ, hΨ⟩
  -- Range elements are fixed points by idempotence.
  have : closeSelector S b RI T.1 = T.1 := by
    calc
      closeSelector S b RI T.1 = closeSelector S b RI (closeSelector S b RI Ψ) := by
        simp [hΨ.symm]
      _ = closeSelector S b RI Ψ := by
        simpa using (closeSelector.idem (S := S) (b := b) (RI := RI) Ψ)
      _ = T.1 := hΨ
  simpa [IsClosed] using this

noncomputable def fixedToRange :
    ClosedSelectorFixed (S := S) (b := b) RI → ClosedSelector (S := S) (b := b) RI := by
  rintro ⟨Φ, hΦ⟩
  refine ⟨Φ, ?_⟩
  refine ⟨Φ, ?_⟩
  simpa [IsClosed] using hΦ

noncomputable def closedRangeEquivFixed :
    ClosedSelector (S := S) (b := b) RI ≃ ClosedSelectorFixed (S := S) (b := b) RI := by
  classical
  refine
    { toFun := rangeToFixed (S := S) (b := b) RI
      invFun := fixedToRange (S := S) (b := b) RI
      left_inv := ?_
      right_inv := ?_ }
  · rintro ⟨Φ, ⟨Ψ, rfl⟩⟩
    apply Subtype.ext
    rfl
  · rintro ⟨Φ, hΦ⟩
    apply Subtype.ext
    rfl

end

end MRSystems
end LoF
end HeytingLean
