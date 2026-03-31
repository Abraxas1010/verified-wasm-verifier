import HeytingLean.LeanCP.Core.HProp
import HeytingLean.LeanCP.Predicates.Array
import HeytingLean.LeanCP.Lang.CSyntax
import HeytingLean.LeanCP.VCG.WP

/-!
# LeanCP Sketch: String Length (Strlen)

Counts the length of a null-terminated string (encoded as an integer array
ending with 0).
```c
/*@ Require arrayAt(s, vs) ∗ ⌜last(vs) = 0⌝ */
/*@ Ensure arrayAt(s, vs) ∗ ⌜__return = indexOf(0, vs)⌝ */
int my_strlen(char *s) {
  int len = 0;
  while (*s != 0) { s++; len++; }
  return len;
}
```
This remains a sketch: the loop invariant is still `HProp.htrue`, and the
postcondition only asserts array preservation (not the functional property
`__return = indexOf(0, vs)`) because LeanCP's assertion layer cannot yet relate
return values to environment-bound parameters.
-/

namespace HeytingLean.LeanCP.Examples

open HeytingLean.LeanCP

def strlenBody : CStmt :=
  .seq (.assign (.var "len") (.intLit 0))
  (.seq (.whileInv
    (.binop .ne (.deref (.var "s")) (.intLit 0))
    HProp.htrue
    (.seq (.assign (.var "s") (.binop .add (.var "s") (.intLit 1)))
          (.assign (.var "len") (.binop .add (.var "len") (.intLit 1)))))
  (.ret (.var "len")))

noncomputable def strlenSpec : CFunSpec where
  name := "my_strlen"
  params := [("s", .ptr .int)]
  retType := .int
  pre := HProp.hexists fun (vs : List CVal) =>
           arrayAt 0 vs
  post := fun _ =>
           HProp.hexists fun (vs : List CVal) =>
             arrayAt 0 vs
  body := strlenBody

example : strlenBody = strlenBody := rfl

end HeytingLean.LeanCP.Examples
