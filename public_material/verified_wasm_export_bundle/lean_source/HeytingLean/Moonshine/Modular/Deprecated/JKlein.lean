import HeytingLean.Moonshine.Modular.JSeries
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

set_option autoImplicit false

namespace HeytingLean.Moonshine.Modular

/--
Interface data for the analytic `J(τ)` function and its q-expansion at infinity.

This is intentionally an interface (no axioms): downstream statements take this as a parameter.
Later, you can instantiate it using mathlib's modular-forms infrastructure.
-/
structure JKleinData where
  J : UpperHalfPlane → ℂ
  qExpansionAtInfty : (UpperHalfPlane → ℂ) → Laurent ℂ
  qExpansion_matches : qExpansionAtInfty J = J_q

end HeytingLean.Moonshine.Modular
