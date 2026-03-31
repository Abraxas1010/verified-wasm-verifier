import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.Dynamics.FixedPoints.Basic

/-!
# (M,R) coalgebra core — reader coalgebras and fixed-point closure (scoped)

This module provides a **minimal, reusable** categorical footprint of the Rosen-style data:

- inputs `A`, configurations/outputs `B`;
- metabolism `M : A → B`;
- repair/transition `R : B → (A → B)`.

Key point:
- `R` is exactly a **coalgebra structure map** for the reader endofunctor `X ↦ (A → X)` on `Type`.

We also package the spec’s “closure” equation as a family of fixed-point conditions.

Objective boundary:
- This file does *not* attempt to encode the Tier-1 admissibility sets (`H`, `Sel`) or to prove any
  “terminal coalgebra” existence theorem.  It is a clean core layer to build on.
-/

namespace HeytingLean
namespace LoF
namespace MRSystems

open CategoryTheory

universe u v

/-! ## Reader endofunctor on `Type` -/

/-- The reader endofunctor `X ↦ (A → X)` on `Type`. -/
def ReaderEndo (A : Type u) : Type (max u v) ⥤ Type (max u v) where
  obj X := A → X
  map {X Y} (f : X → Y) := fun g a => f (g a)
  map_id := by
    intro X
    rfl
  map_comp := by
    intro X Y Z f g
    rfl

/-! ## A minimal (M,R) core and closure as fixed points -/

/-- Minimal Rosen-style (M,R) core data (no admissibility sets). -/
structure MRCore where
  A : Type u
  B : Type v
  /-- Metabolism / initialization. -/
  M : A → B
  /-- Repair / transition: given a configuration, return an `A → B` map. -/
  R : B → (A → B)

namespace MRCore

/-- Spec-faithful “diagonal” closure: each `M a` is a fixed point for input `a`. -/
def ClosedDiag (m : MRCore) : Prop :=
  ∀ a : m.A, m.R (m.M a) a = m.M a

/-- Stronger “uniform” closure: `M a` is stable under *all* inputs. -/
def ClosedAll (m : MRCore) : Prop :=
  ∀ a a' : m.A, m.R (m.M a) a' = m.M a

theorem closedDiag_iff_isFixedPt (m : MRCore) :
    m.ClosedDiag ↔ ∀ a : m.A, Function.IsFixedPt (fun b : m.B => m.R b a) (m.M a) := by
  simp [ClosedDiag, Function.IsFixedPt]

theorem ClosedAll.closedDiag {m : MRCore} (h : m.ClosedAll) : m.ClosedDiag := by
  intro a
  simpa [ClosedAll] using h a a

/-- Package `R` as a coalgebra structure for the reader endofunctor. -/
def toCoalgebra (m : MRCore.{u, v}) :
    CategoryTheory.Endofunctor.Coalgebra (ReaderEndo.{u, v} m.A) where
  V := ULift.{u, v} m.B
  str := fun b => fun a => ULift.up (m.R b.down a)

end MRCore

end MRSystems
end LoF
end HeytingLean
