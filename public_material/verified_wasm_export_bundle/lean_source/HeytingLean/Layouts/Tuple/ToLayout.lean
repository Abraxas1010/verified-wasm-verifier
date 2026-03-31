import HeytingLean.Layouts.Flat.Basic
import HeytingLean.Layouts.Tuple.Category

/-!
# Encoding `Tuple` morphisms as flat layouts

Given a `Tuple` morphism `f : S ⟶ T`, we produce the corresponding flat layout `L_f`:

- shapes are the dimensions of `S`,
- each stride is either `0` (projected dimension) or a prefix product of the dimensions of `T`,
  depending on where the dimension maps.

This matches the flat-case encoding from the CuTe layout-categories presentation.
-/

namespace HeytingLean
namespace Layouts
namespace Tuple

open Flat

namespace Obj

/-- Prefix product of the first `k` dimensions (colex stride for dimension `k`). -/
def prefixProd (T : Obj) (k : ℕ) : ℕ :=
  (T.take k).foldl (fun acc s => acc * s.val) 1

@[simp] theorem prefixProd_zero (T : Obj) : prefixProd T 0 = 1 := by
  simp [prefixProd]

end Obj

namespace Mor

variable {S T : Obj}

/-- The stride assigned to a source dimension `i` by a `Tuple` morphism. -/
def strideAt (f : Mor S T) (i : Fin S.length) : ℕ :=
  match f.hom (some i) with
  | none => 0
  | some j => Obj.prefixProd T j.val

/-- Encode a `Tuple` morphism as a flat layout `L_f`. -/
def toLayout (f : Mor S T) : FlatLayout :=
  List.ofFn (fun i : Fin S.length =>
    (ShapeStridePair.mk (shape := S.get i) (stride := f.strideAt i)))

@[simp] theorem toLayout_length (f : Mor S T) : f.toLayout.length = S.length := by
  simp [toLayout]

end Mor

end Tuple
end Layouts
end HeytingLean

