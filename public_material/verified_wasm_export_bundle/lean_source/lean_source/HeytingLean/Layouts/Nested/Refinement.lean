import Mathlib.Data.List.Basic
import Mathlib.Data.PNat.Defs

import HeytingLean.Layouts.Nested.Profile

/-!
# Refinements of nested tuples + mutual refinement algorithm

This follows the companion implementation in `ColfaxResearch/layout-categories`:
- `NestedTuple.refines` (boolean check, matching the Python definition),
- `relativeMode?` / `sublength?` (used by pullback/pushforward),
- `mutualRefinement?` (Algorithm 4.1.1 style greedy factor splitting).
-/

namespace HeytingLean
namespace Layouts
namespace Nested

namespace NestedTuple

/-! ## Refinement relation (computable) -/

mutual
  /-- Boolean refinement check, matching `NestedTuple.refines` in the Python reference.

  `S` refines `T` if:
  1. `S = T`, or
  2. `T` is a leaf and `T = size(S)`, or
  3. both are nodes of the same rank and refine modewise.
  -/
  def refinesB : NestedTuple → NestedTuple → Bool
    | S, T =>
        if decide (S = T) then
          true
        else
          match T with
          | leaf n => decide (S.size = n.val)
          | node ys =>
              match S with
              | leaf _ => false
              | node xs => refinesListB xs ys

  private def refinesListB : List NestedTuple → List NestedTuple → Bool
    | [], [] => true
    | x :: xs, y :: ys => refinesB x y && refinesListB xs ys
    | _, _ => false
end

/-! ## Relative modes -/

private def findModeIndex? (modes : List NestedTuple) (i : ℕ) : Option (ℕ × ℕ) :=
  let rec go (modes : List NestedTuple) (offset idx : ℕ) : Option (ℕ × ℕ) :=
    match modes with
    | [] => none
    | m :: ms =>
        let len := m.length
        if offset + len < i then
          go ms (offset + len) (idx + 1)
        else
          some (idx, offset)
  go modes 0 0

/-- The `i`-th relative mode of `S` with respect to `T`.

Returns `none` if:
- `i` is out of range for `T.length`, or
- `S` does not refine `T` (as witnessed by `refinesB`).
-/
private def relativeModeFuel? (fuel : ℕ) (S : NestedTuple) (i : ℕ) (T : NestedTuple) : Option NestedTuple := do
  match fuel with
  | 0 => none
  | Nat.succ fuel' =>
      if i = 0 then
        none
      else if T.length < i then
        none
      else if refinesB S T = false then
        none
      else
        match T with
        | leaf _ =>
            if i == 1 then
              some S
            else
              none
        | node ys =>
            match S with
            | leaf _ => none
            | node xs =>
                if xs.length != ys.length then
                  none
                else
                  let (idx, offset) ← findModeIndex? ys i
                  let sMode ← xs[idx]?
                  let tMode ← ys[idx]?
                  relativeModeFuel? fuel' sMode (i - offset) tMode

def relativeMode? (S : NestedTuple) (i : ℕ) (T : NestedTuple) : Option NestedTuple :=
  relativeModeFuel? (T.depth + 1) S i T

/-- Relative flattening (as a nested tuple of length `T.length`). -/
def relativeFlattening? (S : NestedTuple) (T : NestedTuple) : Option NestedTuple := do
  if refinesB S T = false then
    none
  else
    let rec go (i : ℕ) (accRev : List NestedTuple) : Option (List NestedTuple) := do
      match i with
      | 0 => pure accRev.reverse
      | Nat.succ k =>
          let mode ← relativeMode? S (Nat.succ k) T
          go k (mode :: accRev)
    let modes ← go T.length []
    pure (NestedTuple.node modes)

/-- Underlying map of a refinement `S ⟶ T`, as a list of target leaf indices (1-indexed). -/
def underlyingMap? (S : NestedTuple) (T : NestedTuple) : Option (List ℕ) := do
  if refinesB S T = false then
    none
  else
    let rec go (i : ℕ) (acc : List ℕ) : Option (List ℕ) := do
      match i with
      | 0 => pure acc
      | Nat.succ k =>
          let mode ← relativeMode? S (Nat.succ k) T
          let reps : List ℕ := List.replicate mode.length (Nat.succ k)
          go k (reps ++ acc)
    go T.length []

/-- Offset of the refinement block for the `i`-th leaf of `T` inside `S.flatten`.

This is `sum_{j < i} (relativeMode S j T).length`.
-/
def sublength? (S : NestedTuple) (i : ℕ) (T : NestedTuple) : Option ℕ := do
  if i = 0 then
    none
  else if T.length < i then
    none
  else if refinesB S T = false then
    none
  else
    let rec go (j : ℕ) (acc : ℕ) : Option ℕ := do
      if i ≤ j then
        pure acc
      else
        let mode ← relativeMode? S j T
        go (j + 1) (acc + mode.length)
    go 1 0

/-! ## Mutual refinement (Algorithm 4.1.1, executable) -/

private def natToPNat? (n : ℕ) : Option ℕ+ :=
  if h : 0 < n then
    some ⟨n, h⟩
  else
    none

private def factorsToNested? : List ℕ → Option NestedTuple
  | [] => none
  | [n] => do
      let pn ← natToPNat? n
      pure (NestedTuple.leaf pn)
  | ns => do
      let pns ← ns.mapM natToPNat?
      pure (NestedTuple.node (pns.map NestedTuple.leaf))

private structure MutualLoopOut where
  res1Rev : List (List ℕ)
  res2Rev : List (List ℕ)
  remaining2 : List ℕ
  cur2Rev : List ℕ

private def mutualLoop (fuel : ℕ) (list1 list2 : List ℕ)
    (cur1Rev cur2Rev : List ℕ)
    (res1Rev res2Rev : List (List ℕ)) : Option MutualLoopOut := do
  match fuel with
  | 0 => none
  | Nat.succ fuel' =>
      match list1 with
      | [] =>
          if cur1Rev = [] then
            some ⟨res1Rev, res2Rev, list2, cur2Rev⟩
          else
            none
      | a :: as =>
          match list2 with
          | [] => none
          | b :: bs =>
              if a = 0 ∨ b = 0 then
                none
              else if a = b then
                let group1 := (a :: cur1Rev).reverse
                let group2 := (b :: cur2Rev).reverse
                mutualLoop fuel' as bs [] [] (group1 :: res1Rev) (group2 :: res2Rev)
              else if a < b then
                if b % a ≠ 0 then
                  none
                else
                  let group1 := (a :: cur1Rev).reverse
                  mutualLoop fuel' as ((b / a) :: bs) [] (a :: cur2Rev) (group1 :: res1Rev) res2Rev
              else
                -- `b < a` since `a ≠ b` and `¬ a < b`.
                if a % b ≠ 0 then
                  none
                else
                  let group2 := (b :: cur2Rev).reverse
                  mutualLoop fuel' ((a / b) :: as) bs (b :: cur1Rev) [] res1Rev (group2 :: res2Rev)

private def finalizeGroups2? (res2Rev : List (List ℕ)) (remaining2 : List ℕ) (cur2Rev : List ℕ) :
    Option (List (List ℕ)) := do
  match remaining2 with
  | [] =>
      if cur2Rev = [] then
        some res2Rev.reverse
      else
        none
  | b :: bs =>
      let donePrefix := res2Rev.reverse
      if cur2Rev = [] then
        let rest := (b :: bs).map (fun n => [n])
        some (donePrefix ++ rest)
      else
        let groupCur := (b :: cur2Rev).reverse
        let rest := bs.map (fun n => [n])
        some (donePrefix ++ [groupCur] ++ rest)

private def groupsToRepls? (groups : List (List ℕ)) : Option (List NestedTuple) :=
  groups.mapM factorsToNested?

/-- Greedy mutual refinement algorithm (returns `none` on failure). -/
def mutualRefinement? (T U : NestedTuple) : Option (NestedTuple × NestedTuple) := do
  let list1 := T.flattenVals
  let list2 := U.flattenVals
  let fuel := list1.length + list2.length + 1
  let out ← mutualLoop fuel list1 list2 [] [] [] []
  let groups1 := out.res1Rev.reverse
  let groups2 ← finalizeGroups2? out.res2Rev out.remaining2 out.cur2Rev
  let repls1 ← groupsToRepls? groups1
  let repls2 ← groupsToRepls? groups2
  let T' ← T.sub repls1
  let U' ← U.sub repls2
  pure (T', U')

end NestedTuple

end Nested
end Layouts
end HeytingLean
