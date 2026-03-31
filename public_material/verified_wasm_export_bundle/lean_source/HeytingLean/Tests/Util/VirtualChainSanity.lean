import HeytingLean.Util.VirtualChain

/-!
# Tests.Util.VirtualChainSanity

Compile-only checks for the reusable “virtualization via chains” primitive.
-/

namespace HeytingLean.Tests.Util

open HeytingLean.Util

-- A toy step relation on `Nat`.
def Step : Nat → Nat → Prop :=
  fun a b => b = a + 1

abbrev StepChain (a b : Nat) :=
  VirtualChain Step a b

-- A length-2 “virtual arrow” from 0 to 2.
def twoSteps : StepChain 0 2 :=
  VirtualChain.cons (a := 0) (b := 1) (c := 2) rfl (VirtualChain.cons rfl (VirtualChain.nil 2))

-- The “virtual arrows form a category” construction (parameterized by the chosen `Step`).
#check (VirtualChain.category (α := Nat) Step)

end HeytingLean.Tests.Util
