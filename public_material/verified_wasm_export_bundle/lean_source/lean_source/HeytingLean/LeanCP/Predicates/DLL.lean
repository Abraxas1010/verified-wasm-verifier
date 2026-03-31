import HeytingLean.LeanCP.Core.HProp
import HeytingLean.LeanCP.Predicates.Store

/-!
# LeanCP Doubly-Linked List Predicate

`dll addr prev vs` relates a pointer `addr` to a doubly-linked list.
Each node occupies three consecutive heap cells:
  - `addr`   ↦ `CVal.int v`      (data)
  - `addr+1` ↦ `CVal.ptr next`   (next pointer)
  - `addr+2` ↦ `CVal.ptr prev`   (prev pointer)
-/

namespace HeytingLean.LeanCP

/-- Doubly-linked list predicate with back-pointer tracking. -/
def dll : Nat → Nat → List Int → HProp
  | 0, _, [] => HProp.emp
  | 0, _, (_ :: _) => HProp.hfalse
  | _ + 1, _, [] => HProp.hfalse
  | addr + 1, prev, v :: rest =>
      HProp.hexists fun next : Nat =>
        store (addr + 1) (CVal.int v) ∗
        store (addr + 2) (CVal.ptr 0 (Int.ofNat next)) ∗
        store (addr + 3) (CVal.ptr 0 (Int.ofNat prev)) ∗
        dll next (addr + 1) rest

end HeytingLean.LeanCP
