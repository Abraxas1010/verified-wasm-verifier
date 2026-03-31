import HeytingLean.Layouts

/-!
# Layout examples (bundle slice)

Worked examples demonstrating the flat CuTe layout representation
(`HeytingLean.Layouts.Flat.Basic`).

These are intended as small, executable “known-answer tests”.
-/

namespace HeytingLean
namespace Examples
namespace Layouts

open HeytingLean.Layouts
open HeytingLean.Layouts.Flat

private def pnat (n : Nat) (h : 0 < n := by decide) : ℕ+ :=
  ⟨n, h⟩

/-- Row-major 4×4 matrix: strides `[1,4]`. -/
def rowMajor4x4 : FlatLayout :=
  [ShapeStridePair.mk (pnat 4) 1, ShapeStridePair.mk (pnat 4) 4]

/-- Column-major 4×4 matrix: strides `[4,1]`. -/
def colMajor4x4 : FlatLayout :=
  [ShapeStridePair.mk (pnat 4) 4, ShapeStridePair.mk (pnat 4) 1]

/-- Size is 16 for both. -/
example : FlatLayout.size rowMajor4x4 = 16 := by native_decide
example : FlatLayout.size colMajor4x4 = 16 := by native_decide

/-- Rank is 2 for both. -/
example : rowMajor4x4.length = 2 := rfl
example : colMajor4x4.length = 2 := rfl

/-- 3D tensor: 2×3×4. -/
def tensor3D : FlatLayout :=
  [ShapeStridePair.mk (pnat 2) 1, ShapeStridePair.mk (pnat 3) 2, ShapeStridePair.mk (pnat 4) 6]

/-- Size is 24. -/
example : FlatLayout.size tensor3D = 24 := by native_decide

/-- Broadcast layout (stride 0). -/
def broadcast4 : FlatLayout :=
  [ShapeStridePair.mk (pnat 4) 0]

/-- Broadcast has size 4 (but represents 1 stored element). -/
example : FlatLayout.size broadcast4 = 4 := by native_decide

end Layouts
end Examples
end HeytingLean

