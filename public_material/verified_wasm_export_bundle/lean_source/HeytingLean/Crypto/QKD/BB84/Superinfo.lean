import HeytingLean.Constructor.CT.InformationSound
import HeytingLean.Crypto.QKD.BB84.Constructors

/-!
# BB84 as a superinformation medium

We instantiate the `TaskCT.SuperinformationMedium` interface:
- `X` is the Z-basis information variable (clonable).
- `Y` is the X-basis information variable (clonable).
- `XY` is the full BB84 alphabet (not clonable), witnessed by `copyAll_impossible`.
-/

namespace HeytingLean
namespace Crypto
namespace QKD
namespace BB84

open HeytingLean.Constructor.CT

namespace Vars

/-- Single-attribute variable helper. -/
def singletonVar (A : Attribute BB84Substrate) : Variable BB84Substrate where
  attrs := [A]
  pairwiseDisjoint := by
    intro i j hi hj hne
    have hi0 : i = 0 := (Nat.lt_one_iff.mp (by simpa using hi))
    have hj0 : j = 0 := (Nat.lt_one_iff.mp (by simpa using hj))
    exact (hne (by simp [hi0, hj0])).elim

end Vars

/-- Z-basis variable. -/
def zBasisVar : Variable BB84Substrate :=
  Vars.singletonVar attrZBasis

/-- X-basis variable. -/
def xBasisVar : Variable BB84Substrate :=
  Vars.singletonVar attrXBasis

/-- Full BB84 alphabet variable. -/
def fullQubitVar : Variable BB84Substrate :=
  Vars.singletonVar attrAll

/-!
## Information variables
-/

def zBasisInfo : TaskCT.InfoVariable BB84Substrate bb84TaskCT where
  toVariable := zBasisVar
  Perm := Unit
  permTask := fun _ => { arcs := [] }
  perm_possible := by
    intro _
    exact ⟨BB84Ctor.id, BB84Implements.id⟩
  copyTask := copyZ
  copy_possible := copyZ_possible

def xBasisInfo : TaskCT.InfoVariable BB84Substrate bb84TaskCT where
  toVariable := xBasisVar
  Perm := Unit
  permTask := fun _ => { arcs := [] }
  perm_possible := by
    intro _
    exact ⟨BB84Ctor.id, BB84Implements.id⟩
  copyTask := copyX
  copy_possible := copyX_possible

/-- BB84 as a superinformation medium (no-cloning witness is `copyAll_impossible`). -/
def bb84Superinfo : TaskCT.SuperinformationMedium BB84Substrate bb84TaskCT where
  X := zBasisInfo
  Y := xBasisInfo
  XY := fullQubitVar
  copyXY := copyAll
  no_copyXY := copyAll_impossible

end BB84
end QKD
end Crypto
end HeytingLean

