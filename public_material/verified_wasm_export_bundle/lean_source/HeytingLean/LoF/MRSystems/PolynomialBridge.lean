import HeytingLean.LoF.MRSystems.Coalgebra
import HeytingLean.CategoryTheory.Polynomial.Basic
import HeytingLean.Core.Nucleus

namespace HeytingLean
namespace LoF
namespace MRSystems

open CategoryTheory
open CategoryTheory.Polynomial

universe u v

/-- The reader endofunctor `X ↦ (A → X)` as a polynomial `1 · y^A`. -/
def readerPoly (A : Type u) : Poly := PUnit y^A

/-- Object-level equivalence between reader states and polynomial sections. -/
def readerObjEquivApplyFun (A : Type u) (X : Type v) :
    (A → X) ≃ applyFun (readerPoly A) X where
  toFun := fun g => ⟨PUnit.unit, g⟩
  invFun := fun s => s.2
  left_inv := by
    intro g
    rfl
  right_inv := by
    intro s
    cases s with
    | mk p f =>
      cases p
      rfl

/-- Covariant action on polynomial sections induced by a codomain map. -/
def readerPolyMap {A : Type u} {X Y : Type v} (f : X → Y) :
    applyFun (readerPoly A) X → applyFun (readerPoly A) Y :=
  fun s => ⟨s.1, fun a => f (s.2 a)⟩

/-- Natural compatibility between reader-state composition and polynomial action. -/
theorem readerObjEquiv_natural {A : Type u} {X Y : Type v} (f : X → Y) (g : A → X) :
    readerObjEquivApplyFun A Y (fun a => f (g a)) =
      readerPolyMap f (readerObjEquivApplyFun A X g) := by
  rfl

/-- Composition law for polynomial reader actions. -/
theorem readerPolyMap_comp {A : Type u} {X Y Z : Type v}
    (f : X → Y) (g : Y → Z) :
    readerPolyMap (A := A) (g ∘ f) =
      readerPolyMap (A := A) g ∘ readerPolyMap (A := A) f := by
  funext s
  cases s
  rfl

/-- Polynomial section induced by an MR repair map at state `b`. -/
def readerSection (m : MRCore) (b : m.B) : applyFun (readerPoly m.A) m.B :=
  ⟨PUnit.unit, m.R b⟩

/-- Closed-diagonal MR condition in polynomial-section form. -/
theorem closedDiag_iff_readerSection_eval (m : MRCore) :
    m.ClosedDiag ↔ ∀ a : m.A, (readerSection m (m.M a)).2 a = m.M a := by
  simp [MRCore.ClosedDiag, readerSection]

/-- Closed-diagonal MR condition as a polynomial fixed-point statement. -/
theorem closedDiag_iff_readerPoly_fixedPt (m : MRCore) :
    m.ClosedDiag ↔
      ∀ a : m.A, Function.IsFixedPt (fun b : m.B => (readerSection m b).2 a) (m.M a) := by
  simpa [readerSection] using m.closedDiag_iff_isFixedPt

/-- Reinterpret the coalgebra structure map as a polynomial section map. -/
def coalgebraStructAsPoly (m : MRCore.{u, v}) :
    ULift.{u, v} m.B → applyFun (readerPoly m.A) (ULift.{u, v} m.B) :=
  fun b => ⟨PUnit.unit, m.toCoalgebra.str b⟩

/-- Pointwise evaluation of the coalgebra-to-polynomial bridge. -/
theorem coalgebraStructAsPoly_eval (m : MRCore.{u, v}) (b : ULift.{u, v} m.B) (a : m.A) :
    (coalgebraStructAsPoly m b).2 a = ULift.up (m.R b.down a) := by
  rfl

/-- The coalgebra map coincides with the reader-object equivalence packaging. -/
theorem coalgebraStruct_poly_equiv (m : MRCore.{u, v}) (b : ULift.{u, v} m.B) :
    readerObjEquivApplyFun m.A (ULift.{u, v} m.B) (m.toCoalgebra.str b) =
      coalgebraStructAsPoly m b := by
  cases b
  simp [readerObjEquivApplyFun, coalgebraStructAsPoly]

/-- A coalgebra for a polynomial endofunctor. -/
structure PolyCoalgebra (P : CategoryTheory.Polynomial.Poly) where
  S : Type u
  step : S → CategoryTheory.Polynomial.applyFun P S

/-- A state is polynomial-fixed when its continuation is constantly itself. -/
def IsPolyFixedPt {P : CategoryTheory.Polynomial.Poly} (c : PolyCoalgebra P) (s : c.S) : Prop :=
  ∀ d : P.dir (c.step s).1, (c.step s).2 d = s

/-- Package an `MRCore` as a polynomial coalgebra for the reader polynomial. -/
def mrToPolyCoalgebra (m : MRCore) : PolyCoalgebra (readerPoly m.A) where
  S := m.B
  step := fun b => ⟨PUnit.unit, m.R b⟩

/-- MR uniform fixed points are states stable under every input. -/
def IsMRUniformFixed (m : MRCore) (b : m.B) : Prop :=
  ∀ a : m.A, m.R b a = b

/-- Polynomial fixed points for `mrToPolyCoalgebra` are exactly MR-uniform fixed points. -/
theorem isPolyFixedPt_mrToPolyCoalgebra_iff_uniform
    (m : MRCore) (b : m.B) :
    IsPolyFixedPt (mrToPolyCoalgebra m) b ↔ ∀ a : m.A, m.R b a = b := by
  constructor
  · intro h a
    exact h a
  · intro h a
    exact h a

/-- MR uniform fixed points coincide with polynomial coalgebra fixed points. -/
theorem isMRUniformFixed_iff_isPolyFixedPt (m : MRCore) (b : m.B) :
    IsMRUniformFixed m b ↔ IsPolyFixedPt (mrToPolyCoalgebra m) b := by
  simpa [IsMRUniformFixed] using
    (isPolyFixedPt_mrToPolyCoalgebra_iff_uniform m b).symm

/-- Any nucleus induces a polynomial coalgebra over the linear polynomial. -/
def nucleusToPolyCoalgebra {L : Type*} [SemilatticeInf L] [OrderBot L]
    (N : Core.Nucleus L) : PolyCoalgebra (CategoryTheory.Polynomial.linear L) where
  S := L
  step := fun x => ⟨x, fun _ => N.R x⟩

/-- For linear polynomials, fixed-point constancy is equivalent to nucleus fixpoint equality. -/
theorem isPolyFixedPt_linear_iff_fixed
    {L : Type*} [SemilatticeInf L] [OrderBot L]
    (N : Core.Nucleus L) (x : L) :
    IsPolyFixedPt (nucleusToPolyCoalgebra N) x ↔ N.R x = x := by
  constructor
  · intro h
    simpa [nucleusToPolyCoalgebra] using h PUnit.unit
  · intro h d
    cases d
    simpa [nucleusToPolyCoalgebra] using h

/-- Nucleus fixed-point membership iff polynomial fixed-point property. -/
theorem nucleus_fixedPt_iff_poly {L : Type*} [SemilatticeInf L] [OrderBot L]
    (N : Core.Nucleus L) (x : L) :
    x ∈ N.fixedPoints ↔ IsPolyFixedPt (nucleusToPolyCoalgebra N) x := by
  constructor
  · intro hx
    have hxR : N.R x = x := (Core.Nucleus.mem_fixedPoints N x).1 hx
    exact (isPolyFixedPt_linear_iff_fixed (N := N) x).2 hxR
  · intro h
    exact (Core.Nucleus.mem_fixedPoints N x).2
      ((isPolyFixedPt_linear_iff_fixed (N := N) x).1 h)

end MRSystems
end LoF
end HeytingLean
