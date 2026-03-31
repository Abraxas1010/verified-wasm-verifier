import Mathlib.Data.List.Basic
import Mathlib.Data.PNat.Defs

/-!
# Nested tuples / profiles (CuTe layouts)

This is a lightweight, executable representation of the paper's nested tuple shapes:
trees whose leaves are positive integers.

The primary operations used by later algorithms are:
- `flatten` (left-to-right enumeration of leaves),
- `size` (product of all leaf values),
- `sub` (substitute a list of shapes for the leaves, in order).
-/

namespace HeytingLean
namespace Layouts
namespace Nested

/-- Nested tuples of positive integers. -/
inductive NestedTuple where
  | leaf : ℕ+ → NestedTuple
  | node : List NestedTuple → NestedTuple
  deriving Repr

mutual
  private def decEqNestedTuple : (a b : NestedTuple) → Decidable (a = b)
    | NestedTuple.leaf n, NestedTuple.leaf m =>
        match decEq n m with
        | isTrue h =>
            isTrue (by cases h; rfl)
        | isFalse h =>
            isFalse (by
              intro hEq
              cases hEq
              exact h rfl)
    | NestedTuple.node xs, NestedTuple.node ys =>
        match decEqList xs ys with
        | isTrue h =>
            isTrue (by cases h; rfl)
        | isFalse h =>
            isFalse (by
              intro hEq
              cases hEq
              exact h rfl)
    | NestedTuple.leaf _, NestedTuple.node _ =>
        isFalse (by intro h; cases h)
    | NestedTuple.node _, NestedTuple.leaf _ =>
        isFalse (by intro h; cases h)

  private def decEqList : (xs ys : List NestedTuple) → Decidable (xs = ys)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
    | x :: xs, y :: ys =>
        match decEqNestedTuple x y with
        | isTrue hxy =>
            match decEqList xs ys with
            | isTrue hrest =>
                isTrue (by cases hxy; cases hrest; rfl)
            | isFalse hrest =>
                isFalse (by
                  intro h
                  cases h
                  exact hrest rfl)
        | isFalse hxy =>
            isFalse (by
              intro h
              cases h
              exact hxy rfl)
end

instance : DecidableEq NestedTuple := decEqNestedTuple

namespace NestedTuple

/-- Flatten a nested tuple to its left-to-right list of leaves. -/
def flatten : NestedTuple → List ℕ+
  | leaf n => [n]
  | node xs => xs.flatMap flatten

/-- Number of leaf entries in `flatten` (a.k.a. the flattened length). -/
def length (t : NestedTuple) : ℕ :=
  t.flatten.length

/-- Number of leaf entries. -/
def leafCount : NestedTuple → ℕ
  | leaf _ => 1
  | node xs => xs.foldl (fun acc t => acc + leafCount t) 0

/-- Number of top-level modes. -/
def rank : NestedTuple → ℕ
  | leaf _ => 1
  | node xs => xs.length

/-- Product of all leaf values (as a natural number). -/
def size : NestedTuple → ℕ
  | leaf n => n.val
  | node xs => xs.foldl (fun acc t => acc * size t) 1

/-- Maximum nesting depth (`leaf` has depth `0`). -/
def depth : NestedTuple → ℕ
  | leaf _ => 0
  | node xs => xs.foldl (fun acc t => max acc (depth t)) 0 + 1

/-- Leafwise map. -/
def mapLeaves (f : ℕ+ → ℕ+) : NestedTuple → NestedTuple
  | leaf n => leaf (f n)
  | node xs => node (xs.map (mapLeaves f))

/-- The `i`-th top-level mode (1-indexed). -/
def mode? (t : NestedTuple) (i : ℕ) : Option NestedTuple :=
  match t, i with
  | leaf n, 1 => some (leaf n)
  | leaf _, _ => none
  | node _, 0 => none
  | node xs, Nat.succ k => xs[k]?

/-- The `i`-th leaf entry in the flattened representation (1-indexed). -/
def entry? (t : NestedTuple) (i : ℕ) : Option ℕ+ :=
  match i with
  | 0 => none
  | Nat.succ k => t.flatten[k]?

private def subAux : NestedTuple → List NestedTuple → Option (NestedTuple × List NestedTuple)
  | leaf _, [] => none
  | leaf _, r :: rs => some (r, rs)
  | node xs, rs => do
      let rec go (xs : List NestedTuple) (rs : List NestedTuple) :
          Option (List NestedTuple × List NestedTuple) := do
        match xs with
        | [] => pure ([], rs)
        | x :: xs' =>
            let (x', rs') ← subAux x rs
            let (xsOut, rsOut) ← go xs' rs'
            pure (x' :: xsOut, rsOut)
      let (xs', rs') ← go xs rs
      pure (node xs', rs')

/-- Substitute a list of nested tuples for the leaves, in order.

Returns `none` if the replacement list does not have exactly `leafCount` elements.
-/
def sub (t : NestedTuple) (repls : List NestedTuple) : Option NestedTuple := do
  let (t', rest) ← subAux t repls
  match rest with
  | [] => some t'
  | _ => none

/-- Flatten to natural numbers (leaf values). -/
def flattenVals (t : NestedTuple) : List ℕ :=
  t.flatten.map (·.val)

end NestedTuple

end Nested
end Layouts
end HeytingLean
