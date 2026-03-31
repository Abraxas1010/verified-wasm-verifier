import HeytingLean.Noneism.Semantics.Sylvan

namespace HeytingLean
namespace Noneism
namespace Tests

open Noneism Sylvan

section
variable {σ D} (M : Sylvan.Model σ D) (ρ : Sylvan.Valuation D)
variable (x : Noneism.Var) (φ : Noneism.Formula σ)

/-- UI sanity: instantiation from a universal holds at any witness. -/
theorem ui_instantiates (d : D) (h : Sylvan.eval M ρ (.pi x φ)) :
    Sylvan.eval M (Sylvan.update ρ x d) φ := by
  exact (Sylvan.ui_pi M ρ x φ h d)

/-- EG sanity: from an existential we get a witness. -/
theorem eg_has_witness (h : Sylvan.eval M ρ (.sigma x φ)) :
    ∃ d : D, Sylvan.eval M (Sylvan.update ρ x d) φ := by
  exact (Sylvan.eg_sigma M ρ x φ h)
end

end Tests
end Noneism
end HeytingLean
