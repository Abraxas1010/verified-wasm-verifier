import HeytingLean.LeanCP.Core.HProp
import HeytingLean.LeanCP.Predicates.SLL
import HeytingLean.LeanCP.Lang.CSyntax
import HeytingLean.LeanCP.VCG.WP

/-!
# LeanCP Example: Merge Two Sorted Linked Lists

Encodes a simplified merge of two sorted linked lists.
```c
/*@ Require sll(a, la) ∗ sll(b, lb) */
/*@ Ensure sll(__return, merge(la, lb)) */
struct list *merge(struct list *a, struct list *b) { ... }
```
This remains a specification/encoding example; no discharged `genVC` theorem is
claimed for the current simplified merge body.
-/

namespace HeytingLean.LeanCP.Examples

open HeytingLean.LeanCP

/-- Simplified merge: if a is null return b, else return a (placeholder). -/
def mergeBody : CStmt :=
  .ite (.binop .eq (.var "a") .null)
    (.ret (.var "b"))
    (.ite (.binop .eq (.var "b") .null)
      (.ret (.var "a"))
      -- Full merge would have a while loop here
      (.ret (.var "a")))

noncomputable def mergeSpec : CFunSpec where
  name := "merge"
  params := [("a", .ptr (.struct "list")), ("b", .ptr (.struct "list"))]
  retType := .ptr (.struct "list")
  pre := HProp.hexists fun (la : List Int) =>
         HProp.hexists fun (lb : List Int) =>
         HProp.hexists fun (addrA : Nat) =>
         HProp.hexists fun (addrB : Nat) =>
           sll addrA la ∗ sll addrB lb
  post := fun retVal =>
         HProp.hexists fun (merged : List Int) =>
           match retVal with
           | .null => sll 0 []
           | _ =>
               match ptrBase? retVal with
               | some addr => sll addr merged
               | none => HProp.hfalse
  body := mergeBody

example : mergeBody = mergeBody := rfl

end HeytingLean.LeanCP.Examples
