import Lean

namespace HeytingLean
namespace Policy

inductive RecipientSpec where
  | all
  | verified
  | custom (ids : List Nat)
  deriving Repr, BEq

open RecipientSpec

def recipientRefines (parent child : RecipientSpec) : Bool :=
  match parent, child with
  | all, _ => true
  | verified, verified => true
  | verified, _ => false
  | custom ps, custom cs =>
      let mem (ys : List Nat) (x : Nat) : Bool := ys.any (fun y => y == x)
      cs.all (fun x => mem ps x)
  | custom _, _ => false

end Policy
end HeytingLean
