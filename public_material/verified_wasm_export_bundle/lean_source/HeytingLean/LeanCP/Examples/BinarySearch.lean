import HeytingLean.LeanCP.Core.HProp
import HeytingLean.LeanCP.Predicates.Array
import HeytingLean.LeanCP.Lang.CSyntax
import HeytingLean.LeanCP.VCG.WP

/-!
# LeanCP Sketch: Binary Search

Binary search on a sorted integer array.
```c
/*@ Require arrayAt(a, vs) ∗ ⌜sorted(vs) ∧ len(vs) = n⌝ */
/*@ Ensure arrayAt(a, vs) ∗ ⌜0 ≤ __return ≤ n⌝ */
int binary_search(int *a, int n, int target) { ... }
```
-/

namespace HeytingLean.LeanCP.Examples

open HeytingLean.LeanCP

def binarySearchBody : CStmt :=
  .seq (.assign (.var "lo") (.intLit 0))
  (.seq (.assign (.var "hi") (.var "n"))
  (.seq (.whileInv (.binop .lt (.var "lo") (.var "hi"))
    HProp.htrue
    (.seq (.assign (.var "mid") (.binop .div
            (.binop .add (.var "lo") (.var "hi")) (.intLit 2)))
    (.ite (.binop .lt (.deref (.binop .add (.var "a") (.var "mid"))) (.var "target"))
      (.assign (.var "lo") (.binop .add (.var "mid") (.intLit 1)))
      (.assign (.var "hi") (.var "mid")))))
  (.ret (.var "lo"))))

noncomputable def binarySearchSpec : CFunSpec where
  name := "binary_search"
  params := [("a", .ptr .int), ("n", .int), ("target", .int)]
  retType := .int
  pre := HProp.hexists fun (vs : List CVal) =>
           arrayAt 0 vs
  post := fun _ => HProp.hexists fun (vs : List CVal) =>
           arrayAt 0 vs
  body := binarySearchBody

example : binarySearchBody = binarySearchBody := rfl

end HeytingLean.LeanCP.Examples
