import HeytingLean.PersistentSheafLaplacian.Basic.Orientation
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace HeytingLean
namespace PersistentSheafLaplacian

open SimplicialComplex

/-- A cellular sheaf on a simplicial complex with forward face-to-coface maps. -/
structure CellularSheaf {V : Type*} [DecidableEq V] (K : SimplicialComplex V) where
  stalkType : K.Simplex → Type*
  addCommGroup : ∀ σ, AddCommGroup (stalkType σ)
  module : ∀ σ, Module ℝ (stalkType σ)
  finiteDimensional : ∀ σ, FiniteDimensional ℝ (stalkType σ)
  restriction : ∀ {σ τ : K.Simplex}, σ ≤ τ → stalkType σ →ₗ[ℝ] stalkType τ
  comp_law :
    ∀ {σ τ ρ : K.Simplex} (hστ : σ ≤ τ) (hτρ : τ ≤ ρ),
      restriction hτρ ∘ₗ restriction hστ =
        restriction (SimplicialComplex.face_trans (K := K) hστ hτρ)

attribute [instance] CellularSheaf.addCommGroup
attribute [instance] CellularSheaf.module
attribute [instance] CellularSheaf.finiteDimensional

namespace CellularSheaf

variable {V : Type*} [DecidableEq V] {K : SimplicialComplex V}

/-- Constant sheaf with identity face maps. -/
def constantSheaf (K : SimplicialComplex V) (W : Type*)
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W] : CellularSheaf K where
  stalkType := fun _ => W
  addCommGroup := fun _ => inferInstance
  module := fun _ => inferInstance
  finiteDimensional := fun _ => inferInstance
  restriction := fun {_σ _τ} _ => LinearMap.id
  comp_law := by
    intro σ τ ρ hστ hτρ
    ext x
    rfl

end CellularSheaf

end PersistentSheafLaplacian
end HeytingLean
