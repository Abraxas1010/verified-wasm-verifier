import HeytingLean.Constructor.CT.Core
import HeytingLean.Crypto.QKD.E91.States

/-!
# E91 tasks (toy, CT-native)

We model three cloning tasks:
- `copyKey`  : copying within the key context (intended possible),
- `copyTest` : copying within the test context (intended possible),
- `copyAll`  : copying across both contexts (intended impossible).
-/

namespace HeytingLean
namespace Crypto
namespace QKD
namespace E91

open HeytingLean.Constructor.CT
open E91State

/-- Substrate for the toy E91 formalization. -/
abbrev E91Substrate : Type := E91State

/-- Disambiguation helper: CT task. -/
abbrev CTask (σ : Type) : Type :=
  HeytingLean.Constructor.CT.Task σ

/-- Attribute for key-context states. -/
def attrKey : Attribute E91Substrate := E91State.keyStates

/-- Attribute for test-context states. -/
def attrTest : Attribute E91Substrate := E91State.testStates

/-- Attribute for all states. -/
def attrAll : Attribute E91Substrate := E91State.allStates

def copyKey : CTask E91Substrate :=
  { arcs := [(attrKey, attrKey)] }

def copyTest : CTask E91Substrate :=
  { arcs := [(attrTest, attrTest)] }

def copyAll : CTask E91Substrate :=
  { arcs := [(attrAll, attrAll)] }

/-- Prepare “some key-context state”. -/
def prepareKey : CTask E91Substrate :=
  { arcs := [(Set.univ, attrKey)] }

/-- Prepare “some test-context state”. -/
def prepareTest : CTask E91Substrate :=
  { arcs := [(Set.univ, attrTest)] }

lemma copyKey_arc : copyKey.arcs = [(attrKey, attrKey)] := rfl
lemma copyTest_arc : copyTest.arcs = [(attrTest, attrTest)] := rfl
lemma copyAll_arc : copyAll.arcs = [(attrAll, attrAll)] := rfl

lemma attrAll_ne_attrKey : attrAll ≠ attrKey :=
  E91State.allStates_ne_keyStates

lemma attrAll_ne_attrTest : attrAll ≠ attrTest :=
  E91State.allStates_ne_testStates

end E91
end QKD
end Crypto
end HeytingLean

