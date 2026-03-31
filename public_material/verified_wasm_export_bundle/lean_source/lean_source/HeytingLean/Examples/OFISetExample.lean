import HeytingLean.Logic.NucleusSet
import HeytingLean.Logic.TransfiniteNucleus

open HeytingLean.Logic
open Set

namespace HeytingLean
namespace Examples

def Uα : Set String := fun s => s = "alpha"

example (S : Set String) : iterateNat (addClosure (σ := String) Uα) 0 S = S := rfl

example (S : Set String) : iterateNat (addClosure (σ := String) Uα) 1 S = S ∪ Uα := by
  simp [iterateNat, addClosure]

example (S : Set String) :
    iterateNat (addClosure (σ := String) Uα) 2 S = S ∪ Uα := by
  simp [iterateNat, addClosure, union_assoc, union_comm, union_left_comm]

end Examples
end HeytingLean

