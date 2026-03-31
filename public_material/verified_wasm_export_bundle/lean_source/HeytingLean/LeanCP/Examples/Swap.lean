import HeytingLean.LeanCP.Core.HProp
import HeytingLean.LeanCP.Predicates.Store
import HeytingLean.LeanCP.Lang.CSyntax
import HeytingLean.LeanCP.VCG.WP

/-!
# LeanCP Example: Swap Two Pointers

Swaps the values at two pointer locations using a temporary variable.
```c
/*@ Require a ↦ va ∗ b ↦ vb */
/*@ Ensure a ↦ vb ∗ b ↦ va */
void swap(int *a, int *b) {
  int tmp = *a;
  *a = *b;
  *b = tmp;
}
```
This is a classic separation logic example: the precondition guarantees
a and b point to disjoint memory, which makes the swap correct.

This file currently encodes the body and heap-level specification only; it does
not yet contain a discharged `genVC` theorem because LeanCP's assertion layer
does not relate heap predicates to the local-variable environment.
-/

namespace HeytingLean.LeanCP.Examples

open HeytingLean.LeanCP

def swapBody : CStmt :=
  -- tmp = *a
  .seq (.assign (.var "tmp") (.deref (.var "a")))
  -- *a = *b
  (.seq (.assign (.deref (.var "a")) (.deref (.var "b")))
  -- *b = tmp
  (.assign (.deref (.var "b")) (.var "tmp")))

noncomputable def swapSpec : CFunSpec where
  name := "swap"
  params := [("a", .ptr .int), ("b", .ptr .int)]
  retType := .void
  pre := HProp.hexists fun (addrA : Nat) =>
         HProp.hexists fun (addrB : Nat) =>
         HProp.hexists fun (va : CVal) =>
         HProp.hexists fun (vb : CVal) =>
           store addrA va ∗ store addrB vb
  post := fun _ =>
         HProp.hexists fun (addrA : Nat) =>
         HProp.hexists fun (addrB : Nat) =>
         HProp.hexists fun (va : CVal) =>
         HProp.hexists fun (vb : CVal) =>
           store addrA vb ∗ store addrB va
  body := swapBody

example : swapBody = swapBody := rfl

end HeytingLean.LeanCP.Examples
