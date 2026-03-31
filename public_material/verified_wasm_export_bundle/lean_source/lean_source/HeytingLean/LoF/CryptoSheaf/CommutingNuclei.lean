import HeytingLean.LoF.Nucleus

/-
CryptoSheaf/CommutingNuclei

Optional convenience record and basic lemmas for commuting reentry nuclei.
We avoid constructing a composed `Reentry` (which would require extra
primordial/counter data) and instead expose the composed operation and its
algebraic laws.
-/

namespace HeytingLean
namespace LoF
namespace CryptoSheaf

open HeytingLean.LoF

variable {α : Type u} [PrimaryAlgebra α]

/-- Two reentry nuclei commute if `R₁ (R₂ x) = R₂ (R₁ x)` for all `x`. -/
structure CommutingNuclei (R₁ R₂ : Reentry α) : Prop where
  commute : ∀ x, R₁ (R₂ x) = R₂ (R₁ x)

namespace CommutingNuclei

variable {R₁ R₂ : Reentry α}

/-- The composed closure operation. -/
def compOp (R₁ R₂ : Reentry α) (_h : CommutingNuclei R₁ R₂) (x : α) : α :=
  R₁ (R₂ x)

/-- Idempotence of the composed operation under the commute law. -/
lemma compOp_idem (h : CommutingNuclei R₁ R₂) (x : α) :
    compOp R₁ R₂ h (compOp R₁ R₂ h x) = compOp R₁ R₂ h x := by
  dsimp [compOp]
  -- R₁ (R₂ (R₁ (R₂ x))) = R₁ (R₂ x)
  have hc := (h.commute (R₂ x)).symm
  have h1 : R₁ (R₂ (R₁ (R₂ x))) = R₁ (R₁ (R₂ (R₂ x))) := by
    simpa using congrArg R₁ hc
  calc
    R₁ (R₂ (R₁ (R₂ x)))
        = R₁ (R₁ (R₂ (R₂ x))) := h1
    _   = R₁ (R₂ (R₂ x)) := by simp
    _   = R₁ (R₂ x) := by simp

/-- Monotonicity of the composed operation. -/
lemma compOp_monotone (h : CommutingNuclei R₁ R₂) :
    Monotone (compOp R₁ R₂ h) := by
  intro x y hxy; dsimp [compOp]
  exact (Reentry.monotone R₁) ((Reentry.monotone R₂) hxy)

end CommutingNuclei

end CryptoSheaf
end LoF
end HeytingLean
