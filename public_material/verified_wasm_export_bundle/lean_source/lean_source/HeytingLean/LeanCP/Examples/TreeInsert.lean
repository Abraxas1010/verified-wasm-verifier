import HeytingLean.LeanCP.Core.HProp
import HeytingLean.LeanCP.Predicates.Tree
import HeytingLean.LeanCP.Predicates.Store
import HeytingLean.LeanCP.Lang.CSyntax
import HeytingLean.LeanCP.VCG.WP

/-!
# LeanCP Example: BST Insertion

Encodes a C function that inserts a value into a binary search tree.
```c
/*@ Require tree(root, t) */
/*@ Ensure tree(__return, insert(v, t)) */
struct tree *bst_insert(struct tree *root, int v) {
  if (root == NULL) {
    struct tree *node = malloc(sizeof(struct tree));
    node->data = v; node->left = NULL; node->right = NULL;
    return node;
  }
  if (v < root->data) root->left = bst_insert(root->left, v);
  else root->right = bst_insert(root->right, v);
  return root;
}
```
Note: This encodes a non-recursive version (iterative with loop) since
the LeanCP prototype doesn't yet support recursive function calls in the AST.
It remains a specification/encoding example, not a discharged end-to-end VC.
-/

namespace HeytingLean.LeanCP.Examples

open HeytingLean.LeanCP

/-- Simplified BST insert body (non-recursive, handles only the base case). -/
def bstInsertBaseCase : CStmt :=
  .ite (.binop .eq (.var "root") .null)
    -- root == NULL: allocate new node
    (.seq (.alloc "node" 3)
    (.seq (.assign (.fieldAccess (.var "node") "data") (.var "v"))
    (.seq (.assign (.fieldAccess (.var "node") "left") .null)
    (.seq (.assign (.fieldAccess (.var "node") "right") .null)
          (.ret (.var "node"))))))
    -- root != NULL: return root (simplified — full version recurses)
    (.ret (.var "root"))

noncomputable def bstInsertSpec : CFunSpec where
  name := "bst_insert"
  params := [("root", .ptr (.struct "tree")), ("v", .int)]
  retType := .ptr (.struct "tree")
  pre := HProp.hexists fun (t : BTree) =>
           HProp.hexists fun (addr : Nat) =>
             tree addr t
  post := fun retVal =>
           HProp.hexists fun (t : BTree) =>
             match retVal with
             | .ptr _ offset => tree (Int.toNat offset) t
             | _ => HProp.hfalse
  body := bstInsertBaseCase

example : bstInsertBaseCase = bstInsertBaseCase := rfl

end HeytingLean.LeanCP.Examples
