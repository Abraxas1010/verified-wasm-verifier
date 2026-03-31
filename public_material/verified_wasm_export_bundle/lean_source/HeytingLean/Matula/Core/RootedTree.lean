namespace HeytingLean
namespace Matula

/-- Rooted trees for Matula encoding. Children are represented as a list. -/
inductive RTree where
  | leaf : RTree
  | node : List RTree → RTree
  deriving Repr, Inhabited, BEq

mutual
  private def rtreeDecEq : (a b : RTree) → Decidable (a = b)
    | .leaf, .leaf => isTrue rfl
    | .leaf, .node _ => isFalse (by intro h; cases h)
    | .node _, .leaf => isFalse (by intro h; cases h)
    | .node xs, .node ys =>
        match rtreeListDecEq xs ys with
        | isTrue h =>
            isTrue (by cases h; rfl)
        | isFalse h =>
            isFalse (by
              intro hxy
              cases hxy
              exact h rfl)

  private def rtreeListDecEq : (xs ys : List RTree) → Decidable (xs = ys)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
    | x :: xs, y :: ys =>
        match rtreeDecEq x y, rtreeListDecEq xs ys with
        | isTrue hxy, isTrue hrest =>
            isTrue (by cases hxy; cases hrest; rfl)
        | isFalse hxy, _ =>
            isFalse (by
              intro h
              cases h
              exact hxy rfl)
        | _, isFalse hrest =>
            isFalse (by
              intro h
              cases h
              exact hrest rfl)
end

instance : DecidableEq RTree := rtreeDecEq

/-- Rooted forests are lists of rooted trees. -/
abbrev RForest := List RTree

/-- Number of vertices in a rooted tree. -/
def RTree.size : RTree → Nat
  | .leaf => 1
  | .node children => 1 + children.foldl (fun acc t => acc + t.size) 0

/-- Height of a rooted tree. -/
def RTree.height : RTree → Nat
  | .leaf => 0
  | .node children => 1 + children.foldl (fun acc t => max acc t.height) 0

/-- Number of leaf vertices in a rooted tree. -/
def RTree.leaves : RTree → Nat
  | .leaf => 1
  | .node children => children.foldl (fun acc t => acc + t.leaves) 0

/--
Structural canonicalization:
- recursively canonicalize children
- collapse empty nodes (`.node []`) to `.leaf` so the tree carrier does not
  contain two distinct representatives for the single-vertex tree
-/
def RTree.canonicalize : RTree → RTree
  | .leaf => .leaf
  | .node children =>
      let children' := children.map canonicalize
      if children'.isEmpty then .leaf else .node children'

end Matula
end HeytingLean
