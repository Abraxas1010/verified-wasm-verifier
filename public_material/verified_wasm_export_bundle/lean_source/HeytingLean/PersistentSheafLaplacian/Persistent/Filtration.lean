import HeytingLean.PersistentSheafLaplacian.Basic.SimplicialComplex

namespace HeytingLean
namespace PersistentSheafLaplacian

open SimplicialComplex

namespace Persistent

variable {V : Type*} [DecidableEq V]

/-- A simplicial filtration indexed by a linearly ordered parameter set. -/
structure Filtration (I : Type*) [LinearOrder I] where
  complex : I → SimplicialComplex V
  mono : ∀ {r s : I}, r ≤ s → (complex r).IsSubcomplex (complex s)

/-- Lift a simplex across a subcomplex inclusion. -/
def inclusionSimplex {X Y : SimplicialComplex V} (hXY : X.IsSubcomplex Y) :
    X.Simplex → Y.Simplex := fun σ => ⟨σ.1, hXY σ.2⟩

@[simp] theorem inclusionSimplex_val {X Y : SimplicialComplex V} (hXY : X.IsSubcomplex Y)
    (σ : X.Simplex) :
    (inclusionSimplex hXY σ).1 = σ.1 :=
  rfl

theorem inclusionSimplex_face {X Y : SimplicialComplex V} (hXY : X.IsSubcomplex Y)
    {σ τ : X.Simplex} (hστ : σ ≤ τ) :
    inclusionSimplex hXY σ ≤ inclusionSimplex hXY τ :=
  hστ

/-- Lift a `q`-simplex across a subcomplex inclusion. -/
def inclusionqSimplex {X Y : SimplicialComplex V} (hXY : X.IsSubcomplex Y) (q : Nat) :
    X.qSimplices q → Y.qSimplices q
  | ⟨σ, hσ⟩ =>
      ⟨inclusionSimplex hXY σ, by
        rw [SimplicialComplex.mem_qSimplices (K := X)] at hσ
        exact (SimplicialComplex.mem_qSimplices (K := Y)).2 hσ⟩

@[simp] theorem inclusionqSimplex_val {X Y : SimplicialComplex V} (hXY : X.IsSubcomplex Y)
    (q : Nat) (σ : X.qSimplices q) :
    (inclusionqSimplex hXY q σ).1.1 = σ.1.1 :=
  rfl

end Persistent

end PersistentSheafLaplacian
end HeytingLean
