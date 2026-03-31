import HeytingLean.Constructor.CT.InformationSound
import HeytingLean.Crypto.QKD.E91.Constructors

/-!
# E91 as a superinformation medium (toy witness)

We instantiate `TaskCT.SuperinformationMedium`:
- `X` is the key-context information variable (clonable),
- `Y` is the test-context information variable (clonable),
- `XY` is the combined alphabet, whose copy task is impossible.
-/

namespace HeytingLean
namespace Crypto
namespace QKD
namespace E91

open HeytingLean.Constructor.CT

namespace Vars

def singletonVar (A : Attribute E91Substrate) : Variable E91Substrate where
  attrs := [A]
  pairwiseDisjoint := by
    intro i j hi hj hne
    have hi0 : i = 0 := (Nat.lt_one_iff.mp (by simpa using hi))
    have hj0 : j = 0 := (Nat.lt_one_iff.mp (by simpa using hj))
    exact (hne (by simp [hi0, hj0])).elim

end Vars

def keyVar : Variable E91Substrate :=
  Vars.singletonVar attrKey

def testVar : Variable E91Substrate :=
  Vars.singletonVar attrTest

def fullVar : Variable E91Substrate :=
  Vars.singletonVar attrAll

def keyInfo : TaskCT.InfoVariable E91Substrate e91TaskCT where
  toVariable := keyVar
  Perm := Unit
  permTask := fun _ => { arcs := [] }
  perm_possible := by
    intro _
    exact ⟨E91Ctor.id, E91Implements.id⟩
  copyTask := copyKey
  copy_possible := copyKey_possible

def testInfo : TaskCT.InfoVariable E91Substrate e91TaskCT where
  toVariable := testVar
  Perm := Unit
  permTask := fun _ => { arcs := [] }
  perm_possible := by
    intro _
    exact ⟨E91Ctor.id, E91Implements.id⟩
  copyTask := copyTest
  copy_possible := copyTest_possible

def e91Superinfo : TaskCT.SuperinformationMedium E91Substrate e91TaskCT where
  X := keyInfo
  Y := testInfo
  XY := fullVar
  copyXY := copyAll
  no_copyXY := copyAll_impossible

end E91
end QKD
end Crypto
end HeytingLean

