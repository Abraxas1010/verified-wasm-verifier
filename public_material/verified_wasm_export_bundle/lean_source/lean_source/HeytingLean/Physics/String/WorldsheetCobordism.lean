import Mathlib.CategoryTheory.Category.Basic
import HeytingLean.IteratedVirtual.Spiral
import HeytingLean.Physics.String.DBrane
import HeytingLean.Physics.String.Moduli

/-!
# WorldsheetCobordism (Track A)

Executable-first “worldsheet as compositional object” scaffold.

This is intentionally *not* a geometric manifold formalization.
Instead, it packages:
- boundary profiles (closed loop vs open interval endpoints labeled by branes),
- a compositional worldsheet witness (with a “sewing” operation),
- and a spiral/helix visualization map based on compositional length.

The goal is to provide a stable API layer that can later be instantiated
by genuine surface geometry (Track B), while remaining runnable today.
-/

namespace HeytingLean
namespace Physics
namespace String

open HeytingLean.IteratedVirtual

inductive Boundary where
  | closed : Boundary
  | open (left right : Brane) : Boundary
deriving Repr, DecidableEq

inductive Generator where
  | S : Generator
  | T : Generator
deriving Repr, DecidableEq

/-- A compositional “worldsheet” from `A` to `B`.

`gens` is a chain of abstract generators that we can interpret later as
semantic operators (e.g. modular S/T moves, sewing steps, etc.).

`surface` is a lightweight `RiemannSurface` stub used only to track genus/punctures
under sewing; it is *not* a manifold formalization.
-/
structure Worldsheet (A B : Boundary) where
  surface : RiemannSurface := { genus := 0, punctures := 0 }
  gens : List Generator := []
deriving Repr

namespace Worldsheet

@[simp] def length {A B : Boundary} (W : Worldsheet A B) : Nat :=
  W.gens.length

@[simp] def id (A : Boundary) : Worldsheet A A :=
  { surface := { genus := 0, punctures := 0 }, gens := [] }

@[simp] def sew {A B C : Boundary} (W₁ : Worldsheet A B) (W₂ : Worldsheet B C) : Worldsheet A C :=
  -- NOTE: `HeytingLean.Physics.String.sew : RiemannSurface → RiemannSurface → RiemannSurface`
  -- is a non-associative “puncture-gluing” stub. For the *category* structure below we use an
  -- associative monoidal summary: pointwise addition of genus/punctures.
  { surface :=
      { genus := W₁.surface.genus + W₂.surface.genus
        punctures := W₁.surface.punctures + W₂.surface.punctures
      }
    gens := W₁.gens ++ W₂.gens
  }

@[simp] theorem sew_assoc {A B C D : Boundary}
    (W₁ : Worldsheet A B) (W₂ : Worldsheet B C) (W₃ : Worldsheet C D) :
    sew (sew W₁ W₂) W₃ = sew W₁ (sew W₂ W₃) := by
  cases W₁; cases W₂; cases W₃
  simp [Worldsheet.sew, List.append_assoc, Nat.add_assoc]

@[simp] theorem id_sew {A B : Boundary} (W : Worldsheet A B) :
    sew (id A) W = W := by
  cases W
  simp [Worldsheet.id, Worldsheet.sew]

@[simp] theorem sew_id {A B : Boundary} (W : Worldsheet A B) :
    sew W (id B) = W := by
  cases W
  simp [Worldsheet.id, Worldsheet.sew]

/-- Spiral/helix visualization points for a worldsheet’s compositional length. -/
def spiralPoints {A B : Boundary} (W : Worldsheet A B)
    (step : Float := 0.35) (pitch : Float := 0.15) : List Point3 :=
  IteratedVirtual.embedSteps W.length step pitch

end Worldsheet

/-!
## Boundary as a category

This is a Track-A convenience: “worldsheets” become morphisms.
The resulting category is purely compositional and executable-first.
-/

instance : CategoryTheory.Category Boundary where
  Hom A B := Worldsheet A B
  id A := Worldsheet.id A
  comp W₁ W₂ := Worldsheet.sew W₁ W₂
  id_comp := by intro A B W; simp
  comp_id := by intro A B W; simp
  assoc := by
    intro A B C D W₁ W₂ W₃
    exact Worldsheet.sew_assoc (A := A) (B := B) (C := C) (D := D) W₁ W₂ W₃

end String
end Physics
end HeytingLean
