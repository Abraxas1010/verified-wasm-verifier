import HeytingLean.Physics.String.CFT

/-
Simple modular S/T transforms and a finite closure on partitions.
These are stand-ins to enable executable demos without number theory.
-/

namespace HeytingLean
namespace Physics
namespace String

open HeytingLean.Physics.String

@[simp] def sTransform (Z : Partition) : Partition :=
  -- Simple demo: reverse coefficients to simulate a nontrivial action
  Id.run do
    let mut out : Partition := Array.mkEmpty Z.size
    for i in [:Z.size] do
      out := out.push Z[Z.size - 1 - i]!
    out

@[simp] def tTransform (Z : Partition) : Partition :=
  -- Simple demo: rotate right by 1
  if Z.size = 0 then Z else
  Id.run do
    let mut out : Partition := Array.mkEmpty Z.size
    out := out.push Z[Z.size - 1]!
    for i in [:Z.size - 1] do
      out := out.push Z[i]!
    out

@[simp] def eqPart (A B : Partition) : Bool :=
  if A.size != B.size then false else
  Id.run do
    let n := A.size
    let mut ok := true
    for i in [:n] do
      if A[i]! == B[i]! then
        ok := ok
      else
        ok := false
    return ok

@[simp] def dedup (xs : Array Partition) : Array Partition :=
  Id.run do
    let mut acc : Array Partition := #[]
    for x in xs do
      let mut seen := false
      for y in acc do
        if eqPart x y then seen := true
      if !seen then acc := acc.push x
    acc

@[simp] def closure (Z : Partition) (steps : Nat) : Array Partition :=
  Id.run do
    let mut frontier : Array Partition := #[Z]
    let mut seen : Array Partition := #[]
    for _k in [:steps] do
      let mut next : Array Partition := #[]
      for p in frontier do
        next := next.push (sTransform p)
        next := next.push (tTransform p)
      seen := dedup (seen ++ frontier)
      frontier := dedup next
    dedup (seen ++ frontier)

end String
end Physics
end HeytingLean
