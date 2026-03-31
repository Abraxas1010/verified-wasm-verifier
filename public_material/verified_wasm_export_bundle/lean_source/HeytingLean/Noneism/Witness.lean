import HeytingLean.Noneism.Syntax

/-!
# Noneism.Witness

“Witness requirement” scaffolding for the unified-system spec.

Lean’s constructive meaning already treats a proof goal `⊢ P` as “produce a witness of type `P`”.
This module records a lightweight interface that lets other components (ATP, active inference)
talk about witness obligations uniformly, including for noneist object-language formulas.
-/

namespace HeytingLean
namespace Noneism

/-- A generic witness obligation for a target type. -/
structure WitnessObligation (α : Sort u) where
  witness : α

namespace WitnessObligation

/-- Any inhabited type has a trivial witness obligation. -/
def ofInhabited (α : Type u) [Inhabited α] : WitnessObligation α :=
  ⟨default⟩

end WitnessObligation

/-! ## Noneist object-language witness hooks -/

/-- A witnessed noneist formula: a term is singled out as the intentional “object” of the claim. -/
structure WitnessedFormula (σ : Type) where
  term : Term
  formula : Formula σ

/-- “Witness necessity” hook: every witnessed formula yields an existence-marked formula. -/
def witnessNecessity {σ : Type} (wf : WitnessedFormula σ) : Formula σ :=
  Formula.eExists wf.term

theorem witnessNecessity_self {σ : Type} (wf : WitnessedFormula σ) :
    witnessNecessity wf = witnessNecessity wf := by
  rfl

end Noneism
end HeytingLean

