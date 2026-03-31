import HeytingLean.Noneism.Semantics.Sylvan

namespace HeytingLean
namespace Noneism
namespace Examples

open Noneism Formula Sylvan

/-- Generic “round-square” pattern: a formula conjoined with its negation. -/
def roundSquare {σ} (φ : Formula σ) : Formula σ :=
  .and φ (.not φ)

/-- Under the basic Sylvan semantics, no model can make `φ ∧ ¬φ` true.
This isolates the classical contradiction pattern that motivates the
“round square” terminology. -/
theorem round_square_unsat {σ D}
    (M : Sylvan.Model σ D) (ρ : Sylvan.Valuation D) (φ : Formula σ) :
    ¬ Sylvan.eval M ρ (roundSquare φ) := by
  intro h
  unfold roundSquare at h
  -- Expand evaluation of `φ ∧ ¬φ` and discharge the contradiction.
  change Sylvan.eval M ρ φ ∧ ¬ Sylvan.eval M ρ φ at h
  exact h.2 h.1

end Examples
end Noneism
end HeytingLean
