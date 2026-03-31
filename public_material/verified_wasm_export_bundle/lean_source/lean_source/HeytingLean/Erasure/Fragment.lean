/-
  Fragment tags for controlling compilation scope.

  A fragment provides a decidable membership test (`Bool`) for values of a type.
-/

namespace HeytingLean
namespace Erasure

universe u

/-- Fragment identifier. -/
inductive FragmentId
  | Nat1
  | Nat2
  | List1
  | Bool1
  | Custom (name : String)
deriving DecidableEq, Repr

/-- Fragment membership predicate (to be instantiated per fragment/type). -/
class Fragment (id : FragmentId) (α : Type u) where
  /-- Decidable membership in the fragment. -/
  inFragment : α → Bool

/-- Certified value in a specific fragment. -/
structure FragmentCertified (id : FragmentId) (α : Type u) [Fragment id α] (Spec : α → Prop) where
  val : α
  inFrag : Fragment.inFragment (id := id) val = true
  ok : Spec val

namespace FragmentCertified

/-- Fragment-aware extraction (proofs erased). -/
@[inline] def extract {id : FragmentId} {α : Type u} [Fragment id α]
    {Spec : α → Prop} (fc : FragmentCertified id α Spec) : α :=
  fc.val

end FragmentCertified

end Erasure
end HeytingLean

