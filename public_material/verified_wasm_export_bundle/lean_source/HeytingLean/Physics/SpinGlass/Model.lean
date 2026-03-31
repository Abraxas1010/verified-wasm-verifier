import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic

/-
# Correlated-disorder spin-glass parameter and distribution model

This module provides a minimal, spec-level representation of the
three-parameter correlated-disorder Ising spin-glass model used by the
Chaos & Reentrance lens, together with a lightweight 1D histogram type
for magnetisation / overlap distributions.

It does **not** implement any simulation or physics; those are handled
by external tools and executables. The intent is to give the Lean-side
verifier a precise target for interpreting JSON reports and stating
logical contracts (e.g. reentrance and temperature-chaos predicates).
-/

namespace HeytingLean
namespace Physics
namespace SpinGlass

/-- Parameter triple for the correlated-disorder Ising spin-glass model.

All parameters are taken as non-negative reals at the spec level:

* `β`   – physical (inverse) temperature,
* `βp`  – disorder (inverse) temperature,
* `γ`   – correlation parameter appearing in the auxiliary partition
         function `Z_τ(γ)`.

Special submanifolds of this space (e.g. the Nishimori line and EA
plane) are captured by predicates below. -/
structure SGParams where
  β   : ℝ   -- physical inverse temperature
  βp  : ℝ   -- disorder inverse temperature
  γ   : ℝ   -- correlation parameter

/-- Nishimori line condition: `β = γ`. -/
def NL_beta_eq_gamma (p : SGParams) : Prop :=
  p.β = p.γ

/-- Edwards–Anderson (EA) plane condition: `γ = βp`. -/
def EA_plane (p : SGParams) : Prop :=
  p.γ = p.βp

/-- A simple 1D histogram-type distribution, intended for magnetisation
and overlap distributions `P₁`, `P₂`.

* `bins` – bin centres (in ℝ),
* `mass` – non-negative bin weights,
* `norm` – certification that the total mass (viewed in ℝ) sums to `1`.

This is deliberately lightweight: all higher-level semantics (e.g.
“concentrated near zero”) are built in later modules. -/
structure Dist where
  /-- Bin centres in ℝ (e.g. magnetisation or overlap values). -/
  bins : List ℝ
  /-- Bin weights; recorded as reals with an explicit nonnegativity
      certificate rather than a specialised nonnegative type to keep
      dependencies light. -/
  mass : List ℝ
  /-- Every bin weight is nonnegative. -/
  mass_nonneg : ∀ m ∈ mass, 0 ≤ m
  /-- Total mass is normalised to `1`. -/
  norm : mass.sum = 1

end SpinGlass
end Physics
end HeytingLean
