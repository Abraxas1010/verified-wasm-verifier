import Mathlib.Data.PNat.Defs
import Mathlib.Data.List.Basic

/-!
# CuTe layouts: flat core

This is the computational core for *flat* CuTe layouts:

- a flat layout is a list of `(shape, stride)` pairs;
- `toCoords` computes colexicographic coordinates from a linear index (shape-only);
- `apply` evaluates a layout (dot product of coordinates with strides);
- `applyIndex` combines both to give the “layout function” on linear indices.

This file is intentionally *algorithmic first* (executable definitions + small lemmas),
so later categorical structure can reuse it.
-/

namespace HeytingLean
namespace Layouts
namespace Flat

/-! ## Shape/stride pairs -/

/-- A shape/stride pair `(s, d)` where `s : ℕ+` is a positive shape and `d : ℕ` is a stride. -/
structure ShapeStridePair where
  shape : ℕ+
  stride : ℕ
  deriving DecidableEq, Repr

namespace ShapeStridePair

def shapeNat (p : ShapeStridePair) : ℕ := p.shape.val

/-- The “extent” used in tractability constraints (`s * d`). -/
def extent (p : ShapeStridePair) : ℕ := p.shapeNat * p.stride

@[simp] theorem shapeNat_mk (s : ℕ+) (d : ℕ) : (ShapeStridePair.mk s d).shapeNat = s.val := rfl
@[simp] theorem extent_mk (s : ℕ+) (d : ℕ) : (ShapeStridePair.mk s d).extent = s.val * d := rfl

end ShapeStridePair

/-! ## Flat layouts -/

/-- A flat layout is a list of shape/stride pairs. -/
abbrev FlatLayout := List ShapeStridePair

namespace FlatLayout

/-- Shapes of a flat layout. -/
def shapes (L : FlatLayout) : List ℕ+ :=
  L.map (·.shape)

/-- Strides of a flat layout. -/
def strides (L : FlatLayout) : List ℕ :=
  L.map (·.stride)

/-- Size of a flat layout: product of all shapes. -/
def size (L : FlatLayout) : ℕ :=
  L.foldl (fun acc p => acc * p.shapeNat) 1

@[simp] theorem size_nil : size ([] : FlatLayout) = 1 := rfl

/-- Convert a linear index to colex coordinates (shape-only).

This ignores strides; it is the standard “unranking” procedure for a mixed radix numeral system
with radices given by the shapes.
-/
def toCoords : FlatLayout → ℕ → List ℕ
  | [], _ => []
  | p :: ps, i =>
      let s := p.shapeNat
      (i % s) :: toCoords ps (i / s)

theorem toCoords_length (L : FlatLayout) (i : ℕ) : (toCoords L i).length = L.length := by
  induction L generalizing i with
  | nil => simp [toCoords]
  | cons p ps ih =>
      simp [toCoords, ih]

/-- Evaluate a flat layout on an explicit coordinate vector.

If the coordinate list is shorter than the layout rank, missing coordinates are treated as `0`.
Extra coordinates are ignored.
-/
def apply : FlatLayout → List ℕ → ℕ
  | [], _ => 0
  | _ :: ps, [] => apply ps []
  | p :: ps, x :: xs => x * p.stride + apply ps xs

@[simp] theorem apply_nil (xs : List ℕ) : apply ([] : FlatLayout) xs = 0 := rfl

/-- The “layout function” on linear indices: `Φ_L(i) := apply L (toCoords L i)`. -/
def applyIndex (L : FlatLayout) (i : ℕ) : ℕ :=
  apply L (toCoords L i)

end FlatLayout

end Flat
end Layouts
end HeytingLean
