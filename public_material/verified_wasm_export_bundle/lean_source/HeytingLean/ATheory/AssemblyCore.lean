import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Union
import Mathlib.Data.List.Basic

/-
# AssemblyCore: Objects, rules, and assembly index

This module provides a minimal, type-correct scaffold for Assembly Theory:
an alphabet of primitive parts, binary assembly rules, a syntax of objects,
finite assembly paths, and an assembly index defined as the infimum of path
lengths. The definitions are intentionally lightweight and proof obligations
will be developed in later phases.
-/

namespace HeytingLean
namespace ATheory

universe u

/-- Alphabet of primitive parts for assembly. -/
structure Alphabet (α : Type u) where
  basis : Finset α

/-- Binary assembly rule set: given two parts, return the finite set of
admissible composites. -/
structure Rules (α : Type u) where
  compose : α → α → Finset α

/-- Abstract syntax of assembly objects built from primitive parts. -/
inductive Obj (α : Type u) where
  | base : α → Obj α
  | join : Obj α → Obj α → Obj α
deriving Repr, DecidableEq

namespace Obj

variable {α : Type u}

/-- All (syntactic) subobjects of an `Obj`, as a finite set.

This is used to model *reuse* by identifying equal subtrees.
-/
def subobjects [DecidableEq α] : Obj α → Finset (Obj α)
  | base a => {base a}
  | join x y => insert (join x y) (subobjects x ∪ subobjects y)

/-- Predicate: the object is a `join` node. -/
def isJoin : Obj α → Bool
  | base _ => false
  | join _ _ => true

lemma isJoin_iff {o : Obj α} : isJoin o = true ↔ (∃ x y, o = join x y) := by
  cases o <;> simp [isJoin]

/-- Count the number of join-nodes in an object as a simple structural size
measure. This is a fallback notion of length when no explicit path is given. -/
def joinCount : Obj α → Nat
  | base _    => 0
  | join x y  => joinCount x + joinCount y + 1

/-- Reuse-aware join count: count the number of *distinct* `join` subobjects.

This models the standard Assembly Theory convention that already-built
intermediates may be reused at zero additional join-cost.

For example, `join t t` has structural `joinCount = 2 * joinCount t + 1` but
reuse-aware `dagJoinCount = dagJoinCount t + 1`.
-/
def dagJoinCount [DecidableEq α] (o : Obj α) : Nat :=
  ((subobjects o).filter (fun t => isJoin t)).card

theorem dagJoinCount_le_joinCount [DecidableEq α] (o : Obj α) :
    dagJoinCount o ≤ joinCount o := by
  classical
  induction o with
  | base a =>
      simp [dagJoinCount, subobjects, isJoin, joinCount]
  | join x y ihx ihy =>
      -- Expand the definition of `dagJoinCount` and bound the cardinality using
      -- `card_insert_le` and `card_union_le`.
      have h0 :
          (((subobjects (α := α) x).filter (fun t => isJoin t)) ∪
                ((subobjects (α := α) y).filter (fun t => isJoin t))).card
            ≤ ((subobjects (α := α) x).filter (fun t => isJoin t)).card +
                ((subobjects (α := α) y).filter (fun t => isJoin t)).card := by
        simpa using
          (Finset.card_union_le ((subobjects (α := α) x).filter (fun t => isJoin t))
            ((subobjects (α := α) y).filter (fun t => isJoin t)))
      have h1 :
          ((subobjects (α := α) x ∪ subobjects (α := α) y).filter (fun t => isJoin t)).card
            ≤ ((subobjects (α := α) x).filter (fun t => isJoin t)).card +
                ((subobjects (α := α) y).filter (fun t => isJoin t)).card := by
        simpa [Finset.filter_union] using h0
      have h2 :
          (insert (join x y) ((subobjects (α := α) x ∪ subobjects (α := α) y).filter (fun t => isJoin t))).card
            ≤ ((subobjects (α := α) x ∪ subobjects (α := α) y).filter (fun t => isJoin t)).card + 1 := by
        simpa using
          (Finset.card_insert_le (a := join x y)
            (s := ((subobjects (α := α) x ∪ subobjects (α := α) y).filter (fun t => isJoin t))))
      have h3 :
          dagJoinCount (join x y) ≤
            ((subobjects (α := α) x).filter (fun t => isJoin t)).card +
              ((subobjects (α := α) y).filter (fun t => isJoin t)).card + 1 := by
        -- Rewrite the filtered subobjects of `join x y` into an `insert` form.
        have :
            ((subobjects (α := α) (join x y)).filter (fun t => isJoin t)) =
              insert (join x y) ((subobjects (α := α) x ∪ subobjects (α := α) y).filter (fun t => isJoin t)) := by
          simp [subobjects, Finset.filter_insert, isJoin]
        -- Use `h2` and then `h1`.
        have h2' :
            ((subobjects (α := α) (join x y)).filter (fun t => isJoin t)).card
              ≤ ((subobjects (α := α) x ∪ subobjects (α := α) y).filter (fun t => isJoin t)).card + 1 := by
          simpa [this] using h2
        have :
            ((subobjects (α := α) x ∪ subobjects (α := α) y).filter (fun t => isJoin t)).card + 1
              ≤ ((subobjects (α := α) x).filter (fun t => isJoin t)).card +
                  ((subobjects (α := α) y).filter (fun t => isJoin t)).card + 1 := by
          exact Nat.add_le_add_right h1 1
        have h := le_trans h2' this
        simpa [dagJoinCount] using h
      -- Finish by applying the induction hypotheses.
      have hx : ((subobjects (α := α) x).filter (fun t => isJoin t)).card ≤ joinCount x := by
        simpa [dagJoinCount] using ihx
      have hy : ((subobjects (α := α) y).filter (fun t => isJoin t)).card ≤ joinCount y := by
        simpa [dagJoinCount] using ihy
      have hsum :
          ((subobjects (α := α) x).filter (fun t => isJoin t)).card +
              ((subobjects (α := α) y).filter (fun t => isJoin t)).card + 1
            ≤ joinCount x + joinCount y + 1 := by
        exact Nat.add_le_add_right (Nat.add_le_add (by simpa using hx) (by simpa using hy)) 1
      -- Combine.
      have : dagJoinCount (join x y) ≤ joinCount x + joinCount y + 1 :=
        le_trans h3 hsum
      simpa [joinCount] using this

end Obj

/-- Assembly paths are represented as finite lists of objects together with
the declared target. The `wellFormed` predicate checks that every adjacent
pair of objects in the list is compatible with the assembly rules: each edge
`p ⟶ q` must arise from a single admissible composition step. -/
structure Path (α : Type u) (R : Rules α) (target : Obj α) where
  nodes : List (Obj α)
  /-- For every adjacent pair `p, q` in the node list, there are primitive
  parts `a, b` and a composite `c` such that `p` is the join of the bases
  of `a` and `b`, `q` is the base of `c`, and `c` appears in `R.compose a b`. -/
  wellFormed :
    ∀ {p q}, (p, q) ∈ (nodes.zip nodes.tail) →
      ∃ a b c,
        p = Obj.join (Obj.base a) (Obj.base b) ∧
        q = Obj.base c ∧
        c ∈ R.compose a b
  /-- Path length, currently defined as the length of the node list. -/
  len   : Nat := nodes.length

namespace Path

variable {α : Type u} {R : Rules α} {o : Obj α}

/-- A trivial path consisting only of the target object. This witnesses that
every object has at least a degenerate path, so the index is always defined. -/
def trivial (o : Obj α) : Path α R o where
  nodes := [o]
  wellFormed := by
    intro p q hmem
    -- There are no adjacent pairs in a singleton list.
    simp [List.zip, List.tail] at hmem

@[simp] lemma trivial_len (o : Obj α) :
    (trivial (R := R) o).len = 1 := rfl

end Path

/-- Canonical assembly path for an object, built purely from its syntax.

For now this path does not depend on the rule set `R` and simply records the
object once; its length is taken to be the structural join-count. This makes
`syntacticIndex` path-based while remaining lightweight. -/
def canonicalPath {α : Type u} [DecidableEq α] (R : Rules α) (o : Obj α) : Path α R o where
  nodes := [o]
  wellFormed := by
    intro p q hmem
    -- As in `trivial`, there are no adjacent pairs in a singleton list.
    simp [List.zip, List.tail] at hmem
  len   := Obj.dagJoinCount o

/-- **Syntactic index**: the length of a canonical assembly path built from syntax.

**WARNING**: This is NOT the abstract assembly index (which is defined as the
minimum over all valid assembly paths via `Nat.find` in `Paper.AssemblyIndex`).
This is a computable upper bound equal to `Obj.dagJoinCount`.

For the paper-facing min-over-paths definition, see:
`HeytingLean.ATheory.Paper.AssemblySpace.AssemblyIndex.assemblyIndex` -/
def syntacticIndex {α : Type u} [DecidableEq α] (R : Rules α) (o : Obj α) : Nat :=
  (canonicalPath (R := R) o).len

/-- Deprecated alias for `syntacticIndex`. Prefer `syntacticIndex` for clarity. -/
@[deprecated syntacticIndex (since := "2026-01-13")]
def assemblyIndex {α : Type u} [DecidableEq α] (R : Rules α) (o : Obj α) : Nat :=
  syntacticIndex R o

/-- Alias exposing the syntactic index as the "birth-time" of an object in the
Assembly Theory layer. -/
def birthAT {α : Type u} [DecidableEq α] (R : Rules α) (o : Obj α) : Nat :=
  syntacticIndex R o

end ATheory
end HeytingLean
