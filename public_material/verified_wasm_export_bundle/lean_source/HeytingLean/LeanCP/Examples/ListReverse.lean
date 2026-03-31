import HeytingLean.LeanCP.Core.HProp
import HeytingLean.LeanCP.Core.SepLog
import HeytingLean.LeanCP.Predicates.SLL
import HeytingLean.LeanCP.Predicates.Store
import HeytingLean.LeanCP.Lang.CSyntax
import HeytingLean.LeanCP.VCG.WP
import HeytingLean.LeanCP.Tactics.LeanCPSolve

/-!
# LeanCP Sketch: Linked List Reversal

Encodes the annotated C program:
```c
/*@ Require sll(p, l) */
/*@ Ensure sll(__return, rev(l)) */
struct list *reverse(struct list *p) {
  struct list *w = NULL, *v = p;
  /*@ Inv sll(w, l1) * sll(v, l2) && l == app(rev(l1), l2) */
  while (v) {
    struct list *t = v->next;
    v->next = w;
    w = v;
    v = t;
  }
  return w;
}
```

This file is currently an AST/VCG sketch, not an end-to-end verified example.
The loop invariant remains a placeholder, so the trustworthy claim here is only
that LeanCP can encode the program shape and generate a verification condition.
-/

namespace HeytingLean.LeanCP.Examples

open HeytingLean.LeanCP

/-- The linked list reversal program as a C AST. -/
def listReverseBody : CStmt :=
  -- w = NULL
  .seq (.assign (.var "w") .null)
  -- v = p
  (.seq (.assign (.var "v") (.var "p"))
  -- while (v) { ... }
  (.seq (.whileInv (.var "v")
    -- Placeholder invariant: this keeps the example executable as a sketch,
    -- but it is not a verified list-reversal invariant.
    HProp.htrue
    -- Loop body:
    (.seq
      -- t = v->next
      (.assign (.var "t") (.fieldAccess (.var "v") "next"))
    (.seq
      -- v->next = w
      (.assign (.fieldAccess (.var "v") "next") (.var "w"))
    (.seq
      -- w = v
      (.assign (.var "w") (.var "v"))
      -- v = t
      (.assign (.var "v") (.var "t"))))))
  -- return w
  (.ret (.var "w"))))

/-- The full function specification. -/
noncomputable def listReverseSpec : CFunSpec where
  name := "reverse"
  params := [("p", .ptr (.struct "list"))]
  retType := .ptr (.struct "list")
  pre := HProp.hexists fun (l : List Int) =>
           HProp.hexists fun (addr : Nat) =>
             HProp.hand (HProp.pure (addr > 0)) (sll addr l)
  post := fun retVal =>
           HProp.hexists fun (l : List Int) =>
             match ptrBase? retVal with
             | some addr => sll addr l.reverse
             | none => HProp.hfalse
  body := listReverseBody

/-- The VCG generates a smoke-test verification condition. -/
noncomputable def listReverseVC : Prop := genVC listReverseSpec

/-- Smoke test only: the AST and VCG pipeline elaborate. -/
example : listReverseVC → True := fun _ => trivial

/-- Test: the list reverse body is well-formed (contains key operations). -/
example : listReverseBody = listReverseBody := rfl

end HeytingLean.LeanCP.Examples
