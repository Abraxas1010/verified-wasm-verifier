import HeytingLean.Meta.AIT.Prefix

/-
Lightweight, compile-time checks for the AIT prefix core.

These tests exercise the basic `Program`, `IsPrefix`, and
`PrefixFree` definitions on small concrete examples. They are not
meant to be exhaustive; their primary role is to ensure the core
module remains easy to use and stays in sync with the rest of
HeytingLean.
-/

namespace HeytingLean.Tests.AIT

open HeytingLean.Meta.AIT

def pEmpty : Program := []
def pOne   : Program := [true]
def pTwo   : Program := [true, false]

-- Basic checks on the prefix relation and length.
#check IsPrefix.refl (p := pOne)
#check IsPrefix.length_le (p := pOne) (q := pTwo)

-- The example code family is prefix-free.
example : PrefixFree Examples.C₁ :=
  Examples.C₁_prefixFree

end HeytingLean.Tests.AIT

