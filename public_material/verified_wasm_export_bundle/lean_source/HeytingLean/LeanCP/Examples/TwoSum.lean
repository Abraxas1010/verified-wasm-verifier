import HeytingLean.LeanCP.Core.HProp
import HeytingLean.LeanCP.Lang.CSyntax
import HeytingLean.LeanCP.VCG.WP

/-!
# LeanCP Smoke Test: Two Sum (Integer Problem)

A simplified version of the classic LeetCode two-sum problem.
```c
/*@ Require ⌜0 ≤ a ∧ 0 ≤ b⌝ */
/*@ Ensure ⌜__return = a + b⌝ */
int two_sum(int a, int b) { return a + b; }
```

This file is a minimal AST/VCG smoke test; the current heap-only spec surface
cannot yet express the intended return-value relation to the parameter env.
-/

namespace HeytingLean.LeanCP.Examples

open HeytingLean.LeanCP

def twoSumBody : CStmt := .ret (.binop .add (.var "a") (.var "b"))

noncomputable def twoSumSpec : CFunSpec where
  name := "two_sum"
  params := [("a", .int), ("b", .int)]
  retType := .int
  pre := HProp.emp
  post := fun _ => HProp.emp
  body := twoSumBody

example : twoSumBody = twoSumBody := rfl

end HeytingLean.LeanCP.Examples
