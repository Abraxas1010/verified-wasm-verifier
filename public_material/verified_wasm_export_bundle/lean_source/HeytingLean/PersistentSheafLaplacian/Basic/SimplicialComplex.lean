import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Basic

namespace HeytingLean
namespace PersistentSheafLaplacian

/-- A finite abstract simplicial complex on a vertex type `V`. -/
structure SimplicialComplex (V : Type*) [DecidableEq V] where
  /-- The finite set of nonempty simplices. -/
  simplices : Finset (Finset V)
  /-- Every recorded simplex is nonempty. -/
  nonempty_of_mem : ∀ ⦃σ : Finset V⦄, σ ∈ simplices → σ.Nonempty
  /-- The complex is downward-closed under nonempty subsets. -/
  down_closed :
    ∀ ⦃σ : Finset V⦄, σ ∈ simplices →
      ∀ ⦃τ : Finset V⦄, τ ⊆ σ → τ.Nonempty → τ ∈ simplices

namespace SimplicialComplex

variable {V : Type*} [DecidableEq V] (K : SimplicialComplex V)

/-- A simplex of `K` is a simplex together with a proof of membership. -/
abbrev Simplex : Type _ := { σ : Finset V // σ ∈ K.simplices }

/-- The dimension of a simplex is one less than its cardinality. -/
def simplexDim (σ : K.Simplex) : Nat :=
  σ.1.card - 1

/-- The `q`-simplices of `K`. -/
def qSimplices (q : Nat) : Finset K.Simplex :=
  K.simplices.attach.filter (fun σ => σ.1.card = q + 1)

/-- Face relation on simplices: inclusion of underlying finite sets. -/
instance : LE K.Simplex where
  le σ τ := σ.1 ⊆ τ.1

theorem le_def {σ τ : K.Simplex} : σ ≤ τ ↔ σ.1 ⊆ τ.1 := Iff.rfl

theorem simplex_nonempty (σ : K.Simplex) : σ.1.Nonempty :=
  K.nonempty_of_mem σ.2

theorem face_refl (σ : K.Simplex) : σ ≤ σ := by
  intro v hv
  exact hv

theorem face_trans {σ τ ρ : K.Simplex} (hστ : σ ≤ τ) (hτρ : τ ≤ ρ) : σ ≤ ρ := by
  intro v hv
  exact hτρ (hστ hv)

/-- `K₁` is a subcomplex of `K₂` if every simplex of `K₁` is a simplex of `K₂`. -/
def IsSubcomplex (K₁ K₂ : SimplicialComplex V) : Prop :=
  K₁.simplices ⊆ K₂.simplices

theorem mem_qSimplices {q : Nat} {σ : K.Simplex} :
    σ ∈ K.qSimplices q ↔ σ.1.card = q + 1 := by
  simp [qSimplices]

end SimplicialComplex

end PersistentSheafLaplacian
end HeytingLean
