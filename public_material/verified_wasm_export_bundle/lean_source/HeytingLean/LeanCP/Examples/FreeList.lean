import HeytingLean.LeanCP.Core.HProp
import HeytingLean.LeanCP.Predicates.SLL
import HeytingLean.LeanCP.Lang.CSyntax
import HeytingLean.LeanCP.VCG.WP

/-!
# LeanCP Sketch: Free Entire Linked List

Deallocates every node in a singly-linked list.
```c
/*@ Require sll(head, l) */
/*@ Ensure emp */
void free_list(struct list *head) {
  struct list *curr = head;
  while (curr != NULL) {
    struct list *next = curr->next;
    free(curr);
    curr = next;
  }
}
```
This exercises the `free` statement as a shape/ownership sketch. The loop
invariant is still trivial, so the file should not be read as an end-to-end
proof that the list is fully deallocated.
-/

namespace HeytingLean.LeanCP.Examples

open HeytingLean.LeanCP

def freeListBody : CStmt :=
  -- curr = head
  .seq (.assign (.var "curr") (.var "head"))
  -- while (curr != NULL)
  (.whileInv (.binop .ne (.var "curr") .null)
    HProp.htrue
    -- next = curr->next
    (.seq (.assign (.var "next") (.fieldAccess (.var "curr") "next"))
    -- free(curr)
    (.seq (.free (.var "curr") 2)
    -- curr = next
    (.assign (.var "curr") (.var "next")))))

noncomputable def freeListSpec : CFunSpec where
  name := "free_list"
  params := [("head", .ptr (.struct "list"))]
  retType := .void
  pre := HProp.hexists fun (l : List Int) =>
         HProp.hexists fun (addr : Nat) =>
           sll addr l
  post := fun _ => HProp.emp
  body := freeListBody

example : freeListBody = freeListBody := rfl

end HeytingLean.LeanCP.Examples
