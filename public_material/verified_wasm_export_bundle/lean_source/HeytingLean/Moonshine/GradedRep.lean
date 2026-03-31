import HeytingLean.Moonshine.Modular.JSeries
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Trace

set_option autoImplicit false

namespace HeytingLean.Moonshine

open scoped BigOperators

/--
A graded complex representation: `V : ℤ → Type` with finite-dimensional ℂ-vector spaces
and a per-grade representation action.

We include a bounded-below trace condition (via a `lower : ℤ`) so the Thompson series
can be defined as a Hahn series using `HahnSeries.ofSuppBddBelow`.
-/
structure GradedRep (G : Type*) [Group G] where
  V : ℤ → Type*
  instAdd : ∀ n, AddCommGroup (V n)
  instMod : ∀ n, Module ℂ (V n)
  finiteDim : ∀ n, FiniteDimensional ℂ (V n)
  action : ∀ n, G →* (V n →ₗ[ℂ] V n)
  /-- A lower bound so coefficients vanish below it (sufficient to define Hahn series). -/
  lower : ℤ
  /-- For all `g`, the trace coefficient is zero in degrees below `lower`. -/
  trace_eq_zero_of_lt_lower :
    ∀ (g : G) (n : ℤ), n < lower →
      LinearMap.trace ℂ (V n) ((action n) g) = 0

attribute [instance] GradedRep.instAdd GradedRep.instMod GradedRep.finiteDim

/-- The graded dimension in degree `n`. -/
noncomputable def gradedDim {G : Type*} [Group G] (R : GradedRep G) (n : ℤ) : Nat :=
  Module.finrank ℂ (R.V n)

end HeytingLean.Moonshine
