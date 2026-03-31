import HeytingLean.Constructor.CT.Core
import HeytingLean.Crypto.QKD.BB84.States

/-!
# BB84 Tasks

Defines Constructor-Theoretic tasks for the BB84 substrate:
- basis-restricted copying tasks (`copyZ`, `copyX`) intended to be possible;
- universal copying (`copyAll`) intended to be impossible (no-cloning);
- lightweight preparation/measurement tasks (interface-first, used for wiring).
-/

namespace HeytingLean
namespace Crypto
namespace QKD
namespace BB84

open HeytingLean.Constructor.CT
open BB84State

/-- The substrate for BB84 tasks is the finite type of BB84 states. -/
abbrev BB84Substrate : Type := BB84State

/-- Disambiguation helper: CT task (avoids `_root_.Task`). -/
abbrev CTask (σ : Type) : Type :=
  HeytingLean.Constructor.CT.Task σ

/-- Attribute for the Z-basis states. -/
def attrZBasis : Attribute BB84Substrate := BB84State.zBasisStates

/-- Attribute for the X-basis states. -/
def attrXBasis : Attribute BB84Substrate := BB84State.xBasisStates

/-- Attribute for all BB84 states (the full qubit alphabet). -/
def attrAll : Attribute BB84Substrate := BB84State.allStates

/-!
## Copy tasks

At this abstraction layer, copying is represented as a task on attributes.
-/

/-- Copy task restricted to Z-basis states. -/
def copyZ : CTask BB84Substrate :=
  { arcs := [(attrZBasis, attrZBasis)] }

/-- Copy task restricted to X-basis states. -/
def copyX : CTask BB84Substrate :=
  { arcs := [(attrXBasis, attrXBasis)] }

/-- Universal copy task over all BB84 states (intended impossible). -/
def copyAll : CTask BB84Substrate :=
  { arcs := [(attrAll, attrAll)] }

/-!
## Preparation and measurement tasks (interface-first)

We include these to match the BB84 narrative; the security proof below only
needs the cloning tasks.
-/

/-- Prepare a specific BB84 state. -/
def prepareState (target : BB84State) : CTask BB84Substrate :=
  { arcs := [(Set.univ, ({target} : Set BB84Substrate))] }

/-- Prepare “some Z-basis state”. -/
def prepareZ : CTask BB84Substrate :=
  { arcs := [(Set.univ, attrZBasis)] }

/-- Prepare “some X-basis state”. -/
def prepareX : CTask BB84Substrate :=
  { arcs := [(Set.univ, attrXBasis)] }

/-- Measure in Z-basis (projects into Z-basis). -/
def measureZ : CTask BB84Substrate :=
  { arcs := [(attrAll, attrZBasis)] }

/-- Measure in X-basis (projects into X-basis). -/
def measureX : CTask BB84Substrate :=
  { arcs := [(attrAll, attrXBasis)] }

/-!
## Task arc helpers
-/

lemma copyZ_arc : copyZ.arcs = [(attrZBasis, attrZBasis)] := rfl
lemma copyX_arc : copyX.arcs = [(attrXBasis, attrXBasis)] := rfl
lemma copyAll_arc : copyAll.arcs = [(attrAll, attrAll)] := rfl

lemma attrAll_ne_attrZBasis : attrAll ≠ attrZBasis := by
  intro h
  have : ketPlus ∈ attrZBasis := by
    rw [← h]
    exact Set.mem_univ _
  simp [attrZBasis, BB84State.zBasisStates, BB84State.ketPlus] at this

lemma attrAll_ne_attrXBasis : attrAll ≠ attrXBasis := by
  intro h
  have : ket0 ∈ attrXBasis := by
    rw [← h]
    exact Set.mem_univ _
  simp [attrXBasis, BB84State.xBasisStates, BB84State.ket0] at this

end BB84
end QKD
end Crypto
end HeytingLean
