import HeytingLean.LeanCP.Core.HProp
import HeytingLean.LeanCP.Predicates.Array
import HeytingLean.LeanCP.Lang.CSyntax
import HeytingLean.LeanCP.VCG.WP

/-!
# LeanCP Sketch: Array Sum

Encodes a C function that sums the elements of an integer array.
```c
/*@ Require arrayAt(a, vs) ∗ ⌜len(vs) = n⌝ */
/*@ Ensure arrayAt(a, vs) ∗ ⌜__return = sum(vs)⌝ */
int array_sum(int *a, int n) {
  int s = 0, i = 0;
  /*@ Inv arrayAt(a, vs) ∗ ⌜s = sum(take(i, vs))⌝ ∗ ⌜0 ≤ i ≤ n⌝ */
  while (i < n) { s = s + a[i]; i = i + 1; }
  return s;
}
```
This remains a sketch: the loop invariant is still `HProp.htrue`, and the
postcondition only asserts array preservation (not the functional property
`__return = sum(vs)`) because LeanCP's assertion layer cannot yet relate
return values to environment-bound parameters.
-/

namespace HeytingLean.LeanCP.Examples

open HeytingLean.LeanCP

def arraySumBody : CStmt :=
  .seq (.assign (.var "s") (.intLit 0))
  (.seq (.assign (.var "i") (.intLit 0))
  (.seq (.whileInv (.binop .lt (.var "i") (.var "n"))
    HProp.htrue
    (.seq (.assign (.var "s") (.binop .add (.var "s")
            (.deref (.binop .add (.var "a") (.var "i")))))
          (.assign (.var "i") (.binop .add (.var "i") (.intLit 1)))))
  (.ret (.var "s"))))

noncomputable def arraySumSpec : CFunSpec where
  name := "array_sum"
  params := [("a", .ptr .int), ("n", .int)]
  retType := .int
  pre := HProp.hexists fun (vs : List CVal) =>
           arrayAt 0 vs  -- simplified: array at address 0
  post := fun _ =>
           HProp.hexists fun (vs : List CVal) =>
             arrayAt 0 vs
  body := arraySumBody

example : arraySumBody = arraySumBody := rfl

end HeytingLean.LeanCP.Examples
