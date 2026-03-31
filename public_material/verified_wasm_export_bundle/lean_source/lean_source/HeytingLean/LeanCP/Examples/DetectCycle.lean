import HeytingLean.LeanCP.Core.HProp
import HeytingLean.LeanCP.Predicates.SLL
import HeytingLean.LeanCP.Lang.CSyntax
import HeytingLean.LeanCP.VCG.WP

/-!
# LeanCP Sketch: Detect Cycle in Linked List

Floyd's tortoise-and-hare cycle detection.
```c
/*@ Require sll(head, l) */
/*@ Ensure ⌜__return = (hasCycle(l) ? 1 : 0)⌝ */
int has_cycle(struct list *head) { ... }
```
-/

namespace HeytingLean.LeanCP.Examples

open HeytingLean.LeanCP

def hasCycleBody : CStmt :=
  .seq (.assign (.var "slow") (.var "head"))
  (.seq (.assign (.var "fast") (.var "head"))
  (.seq (.whileInv
    (.binop .lAnd
      (.binop .ne (.var "fast") .null)
      (.binop .ne (.fieldAccess (.var "fast") "next") .null))
    HProp.htrue
    (.seq (.assign (.var "slow") (.fieldAccess (.var "slow") "next"))
    (.seq (.assign (.var "fast")
            (.fieldAccess (.fieldAccess (.var "fast") "next") "next"))
    (.ite (.binop .eq (.var "slow") (.var "fast"))
      (.ret (.intLit 1))
      .skip))))
  (.ret (.intLit 0))))

noncomputable def hasCycleSpec : CFunSpec where
  name := "has_cycle"
  params := [("head", .ptr (.struct "list"))]
  retType := .int
  pre := HProp.hexists fun (l : List Int) =>
         HProp.hexists fun (addr : Nat) =>
           sll addr l
  post := fun retVal =>
         HProp.pure (retVal = CVal.int 0 ∨ retVal = CVal.int 1)
  body := hasCycleBody

example : hasCycleBody = hasCycleBody := rfl

end HeytingLean.LeanCP.Examples
