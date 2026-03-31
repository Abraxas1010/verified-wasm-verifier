import HeytingLean.Layouts.Flat.Basic
import HeytingLean.LoF.LoFSecond.Syntax

/-!
# LoF → CuTe syntax generation (bundle slice)

This is a lightweight “generate” direction for a LoF/CuTe bridge.

We use a small, LoF-inspired expression type:

* `void`      → scalar layout (rank 0)
* `mark e`    → prepend a mode of shape 2 with stride = `size` of the inner layout
* `cross a b` → concatenate modes
* `reentry`   → not generatable directly (requires a fixed-point interpretation)
-/

namespace HeytingLean
namespace LoF
namespace CuTe

open HeytingLean.Layouts
open HeytingLean.Layouts.Flat

/-- LoF-shaped expressions used specifically for layout generation. -/
inductive LoFLayoutExpr where
  | void : LoFLayoutExpr
  | mark : LoFLayoutExpr → LoFLayoutExpr
  | cross : LoFLayoutExpr → LoFLayoutExpr → LoFLayoutExpr
  | reentry : LoFLayoutExpr
  deriving Repr, DecidableEq

/-- The scalar layout (rank 0). -/
def scalarLayout : FlatLayout :=
  ([] : FlatLayout)

/-- Shape `2` as a `ℕ+` (used by `mark`). -/
def shape2 : ℕ+ :=
  ⟨2, by decide⟩

/-- The rank (number of modes) of a flat layout. -/
def rank (L : FlatLayout) : Nat :=
  L.length

/-- Generate a flat layout from a LoF-shaped expression. -/
def generateLayout : LoFLayoutExpr → Option FlatLayout
  | .void => some scalarLayout
  | .mark inner => do
      let innerLayout ← generateLayout inner
      -- Mark prepends a mode with shape 2 and stride = size of the inner layout.
      some (ShapeStridePair.mk shape2 (FlatLayout.size innerLayout) :: innerLayout)
  | .cross a b => do
      let layoutA ← generateLayout a
      let layoutB ← generateLayout b
      some (layoutA ++ layoutB)
  | .reentry => none

theorem void_generates_scalar :
    generateLayout .void = some scalarLayout :=
  rfl

/-- Mark increases rank by 1 (for successful generations). -/
theorem mark_increases_rank (e : LoFLayoutExpr) (L : FlatLayout)
    (h : generateLayout e = some L) :
    ∃ L', generateLayout (.mark e) = some L' ∧ rank L' = rank L + 1 := by
  let L' : FlatLayout := ShapeStridePair.mk shape2 (FlatLayout.size L) :: L
  refine ⟨L', ?_, ?_⟩
  · simp [generateLayout, h, L']
  · simp [rank, L']

end CuTe
end LoF
end HeytingLean
