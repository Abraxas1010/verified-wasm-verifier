import HeytingLean.Layouts.Flat.Tractable

/-!
# CuTe layouts: flat complement (with respect to total size `N`)

This implements the executable algorithm `flat_complement` from the companion software
(`ColfaxResearch/layout-categories`), but returns `Option` to account for failed divisibility
preconditions.

The complement is computed on the *sorted* layout (increasing stride, tie-break by shape).

This file also provides a small `squeezeOnes` helper mirroring the `Tuple_morphism.squeeze`
behavior: drop any modes whose shape is `1`.
-/

namespace HeytingLean
namespace Layouts
namespace Flat

open Flat

namespace FlatLayout

/-! ## Helpers -/

private def insertSorted (p : ShapeStridePair) : FlatLayout → FlatLayout
  | [] => [p]
  | q :: qs =>
      if ShapeStridePair.leB p q then
        p :: q :: qs
      else
        q :: insertSorted p qs

/-- Sort a flat layout by `(stride, shape)` (increasing), matching `sort_flat_layout` in the
Python reference implementation. -/
def sortByStride (L : FlatLayout) : FlatLayout :=
  L.foldr insertSorted []

/-- Remove any modes with shape `1` (a flat analogue of `Tuple_morphism.squeeze`). -/
def squeezeOnes (L : FlatLayout) : FlatLayout :=
  L.filter (fun p => decide (p.shapeNat ≠ 1))

private def natToPNat? (n : ℕ) : Option ℕ+ :=
  if h : 0 < n then
    some ⟨n, h⟩
  else
    none

/-! ## Complement -/

/-- Compute the complement of a (sorted) flat layout with respect to total size `N`.

Returns `none` if:
- the sorted layout is empty,
- a required divisor is `0`,
- or a required divisibility check fails.
-/
def complement? (L : FlatLayout) (N : ℕ) : Option FlatLayout := do
  let sorted := sortByStride L
  match sorted with
  | [] => none
  | p0 :: ps =>
      let s0 ← natToPNat? p0.stride

      let rec go (prev : ShapeStridePair) (rest : FlatLayout) (acc : List ℕ+) :
          Option (List ℕ+) := do
        match rest with
        | [] =>
            let denom := prev.shapeNat * prev.stride
            if denom = 0 then
              none
            else if N % denom ≠ 0 then
              none
            else
              let last ← natToPNat? (N / denom)
              some (acc ++ [last])
        | cur :: rest' =>
            let denom := prev.shapeNat * prev.stride
            if denom = 0 then
              none
            else if cur.stride % denom ≠ 0 then
              none
            else
              let next ← natToPNat? (cur.stride / denom)
              go cur rest' (acc ++ [next])

      let shapes ← go p0 ps [s0]
      let strides : List ℕ := 1 :: sorted.map (fun p => p.shapeNat * p.stride)
      pure <| List.zipWith (fun s d => ShapeStridePair.mk (shape := s) (stride := d)) shapes strides

end FlatLayout

end Flat
end Layouts
end HeytingLean

