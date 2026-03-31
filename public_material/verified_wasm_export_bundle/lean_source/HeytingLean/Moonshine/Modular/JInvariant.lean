import HeytingLean.Moonshine.Modular.Eisenstein

set_option autoImplicit false

noncomputable section

namespace HeytingLean.Moonshine.Modular

open UpperHalfPlane

/--
The classical Klein `j`-invariant (as a meromorphic function on `ℍ`), defined via Eisenstein
series:

`j(τ) = 1728 * E4(τ)^3 / (E4(τ)^3 - E6(τ)^2)`.

This file only defines the function; q-expansion and modularity facts are proved elsewhere.
-/
noncomputable def kleinJ (τ : ℍ) : ℂ :=
  (1728 : ℂ) * (E4 τ) ^ 3 / ((E4 τ) ^ 3 - (E6 τ) ^ 2)

/-- The normalized `J(τ) := j(τ) - 744`. -/
noncomputable def kleinJ₀ (τ : ℍ) : ℂ :=
  kleinJ τ - 744

end HeytingLean.Moonshine.Modular

