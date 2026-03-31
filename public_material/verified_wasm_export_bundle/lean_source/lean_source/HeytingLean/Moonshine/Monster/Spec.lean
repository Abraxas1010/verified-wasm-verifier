import HeytingLean.Moonshine.Monster.Constants
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Subgroup.Simple

set_option autoImplicit false

namespace HeytingLean.Moonshine

universe u

/--
A reusable *spec* record for "the Monster group".

This is deliberately abstract: later you can replace axioms with a construction.
-/
structure MonsterSpec where
  M : Type u
  instGroup : Group M
  instFintype : Fintype M
  isSimple : IsSimpleGroup M
  card_eq : Fintype.card M = monsterOrder
  center_trivial : Subgroup.center M = ⊥
  minFaithfulDim : Nat := minFaithfulComplexRepDim

attribute [instance] MonsterSpec.instGroup MonsterSpec.instFintype

end HeytingLean.Moonshine
