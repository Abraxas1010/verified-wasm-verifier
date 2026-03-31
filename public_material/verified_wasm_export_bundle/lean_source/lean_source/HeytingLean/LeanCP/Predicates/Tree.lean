import HeytingLean.LeanCP.Core.HProp
import HeytingLean.LeanCP.Predicates.Store

/-!
# LeanCP Binary Tree Predicate

`tree addr t` relates a pointer `addr` to a logical binary tree `t`.
Each node occupies three consecutive heap cells:
  - `addr`   ↦ `CVal.int v`      (data)
  - `addr+1` ↦ `CVal.ptr left`   (left child, 0 for null)
  - `addr+2` ↦ `CVal.ptr right`  (right child, 0 for null)

Null pointer convention: address 0 represents NULL (leaf/empty tree).
-/

namespace HeytingLean.LeanCP

/-- Logical binary tree structure. -/
inductive BTree where
  | leaf : BTree
  | node : Int → BTree → BTree → BTree
  deriving Repr, DecidableEq, Inhabited

/-- Binary tree heap predicate. -/
def tree : Nat → BTree → HProp
  | 0, .leaf => HProp.emp
  | 0, .node _ _ _ => HProp.hfalse
  | _ + 1, .leaf => HProp.hfalse
  | addr + 1, .node v tl tr =>
      HProp.hexists fun left : Nat =>
      HProp.hexists fun right : Nat =>
        store (addr + 1) (CVal.int v) ∗
        store (addr + 2) (CVal.ptr 0 (Int.ofNat left)) ∗
        store (addr + 3) (CVal.ptr 0 (Int.ofNat right)) ∗
        tree left tl ∗
        tree right tr

theorem tree_leaf (h : Heap) : tree 0 BTree.leaf h ↔ h = Heap.empty := by
  simp [tree, HProp.emp]

theorem tree_null_node (v : Int) (tl tr : BTree) :
    tree 0 (BTree.node v tl tr) = HProp.hfalse := by
  simp [tree]

end HeytingLean.LeanCP
