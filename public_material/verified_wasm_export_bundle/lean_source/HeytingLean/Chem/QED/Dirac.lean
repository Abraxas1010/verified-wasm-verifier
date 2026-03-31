import Mathlib.Algebra.Module.Basic
import HeytingLean.Chem.QED.Spinors

/-!
# Dirac operator interface (minimal coupling skeleton)

At M0 we do not attempt to formalize analysis or PDE solutions. Instead we define a small interface
for "Dirac-like" linear operators on a spinor module, parameterized by charge/mass and by a choice
of gamma representation.
-/

namespace HeytingLean
namespace Chem
namespace QED

universe u

/-- A 4-potential (electromagnetic potential) as a map from indices to scalars, abstractly. -/
structure EMPotential (𝕜 : Type u) (μ : Type u) where
  A : μ → 𝕜

/-- Minimal data for a relativistic charged fermion in an external EM potential. -/
structure DiracParams (𝕜 : Type u) where
  mass   : 𝕜
  charge : 𝕜

/-- A Dirac-like model: a spinor module `S` together with a linear operator `D : S ->ₗ[𝕜] S`.

Later phases can refine `op` into a concrete differential operator with minimal coupling,
and then connect to bound-state Hamiltonians. -/
structure DiracModel (𝕜 : Type u) (μ : Type u) (Aalg : Type u)
    [CommRing 𝕜] [Ring Aalg] [Algebra 𝕜 Aalg] [HasMetric 𝕜 μ] [CliffordRep 𝕜 μ Aalg] where
  S        : Type u
  instAdd  : AddCommGroup S
  instMod  : Module 𝕜 S
  op       : S →ₗ[𝕜] S
  params   : DiracParams 𝕜
  potential : EMPotential 𝕜 μ

attribute [instance] DiracModel.instAdd DiracModel.instMod

end QED
end Chem
end HeytingLean

