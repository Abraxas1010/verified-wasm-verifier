import Mathlib.Data.PNat.Basic
import HeytingLean.Layouts.Flat.Basic

/-!
# CuTe layouts: flat coalesce

`coalesce` merges adjacent modes when they form a contiguous run:

- either both strides are `0` (projected modes), or
- `d₂ = s₁ * d₁` (next stride equals the previous extent).

This is the flat-layout analogue of weak coalescence in the CuTe layout-categories development.
-/

namespace HeytingLean
namespace Layouts
namespace Flat

open Flat

namespace ShapeStridePair

/-- Predicate for when two adjacent modes can be coalesced. -/
def canCoalesce (p q : ShapeStridePair) : Bool :=
  if p.stride == 0 then
    q.stride == 0
  else
    q.stride == p.shapeNat * p.stride

/-- The coalesced pair of two adjacent coalescible pairs.

The resulting stride is the left stride; the resulting shape is the product of shapes.
-/
def coalescePair (p q : ShapeStridePair) : ShapeStridePair :=
  ⟨p.shape * q.shape, p.stride⟩

end ShapeStridePair

namespace FlatLayout

/-- Greedy left-to-right coalescing pass, implemented as a fold. -/
def coalesce (L : FlatLayout) : FlatLayout :=
  (L.foldl
        (fun acc p =>
          match acc with
          | [] => [p]
          | q :: accTail =>
              if ShapeStridePair.canCoalesce q p then
                ShapeStridePair.coalescePair q p :: accTail
              else
                p :: q :: accTail)
        []).reverse

@[simp] theorem coalesce_nil : coalesce ([] : FlatLayout) = [] := by
  simp [coalesce]

end FlatLayout

end Flat
end Layouts
end HeytingLean
