import HeytingLean.Noneism.Bridges.LoFPrimordial

/-!
# Noneism.Core.Nucleus

Compatibility path for Noneist nucleus-facing residuation facts used by LEP tasking.
This module introduces no axioms and re-exports the concrete two-point reentry
instance from `Noneism.Bridges.LoFPrimordial`.
-/

namespace HeytingLean.Noneism.Core

abbrev Omega := HeytingLean.Noneism.Bridge.LoFPrimordial.twoPointReentry.Omega

noncomputable instance : HeytingAlgebra Omega := inferInstance

/-- Noneist residuation law on the concrete two-point reentry carrier. -/
theorem le_himp_iff (a b c : Omega) : a ≤ b ⇨ c ↔ a ⊓ b ≤ c := by
  exact (_root_.le_himp_iff (a := a) (b := b) (c := c))

end HeytingLean.Noneism.Core
