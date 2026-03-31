import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Set.Lattice

/-!
# E91 (toy) state space (interface-first)

This project’s QKD layer is intentionally **interface-first** and CT-native.

For E91, a fully device-independent formalization would require a proper CHSH/Bell
correlation model (Tsirelson bound, monogamy of entanglement, etc.). That is a
substantial standalone development.

This file provides a *minimal, non-trivial substrate* with two incompatible
“contexts” (`key` vs `test`). It supports the same CT pattern as BB84:
- each context is clonable (an information variable),
- their union is not clonable (superinformation witness),
so we can apply the generic no-cloning ⇒ eavesdropping-impossible theorem.
-/

namespace HeytingLean
namespace Crypto
namespace QKD
namespace E91

/-- Two disjoint contexts: key-generation vs CHSH-testing. -/
inductive Context : Type
  | key
  | test
  deriving DecidableEq, Repr

namespace Context

def equivBool : Bool ≃ Context where
  toFun
    | false => key
    | true => test
  invFun
    | key => false
    | test => true
  left_inv b := by cases b <;> rfl
  right_inv c := by cases c <;> rfl

instance : Fintype Context :=
  Fintype.ofEquiv Bool equivBool

end Context

/-- A classical bit. -/
abbrev Bit : Type := Bool

/-- A toy E91 “state”, tagged by context and a bit. -/
structure E91State where
  ctx : Context
  bit : Bit
  deriving DecidableEq, Repr

namespace E91State

def equivProd : (Context × Bit) ≃ E91State where
  toFun p := ⟨p.1, p.2⟩
  invFun s := (s.ctx, s.bit)
  left_inv p := by cases p; rfl
  right_inv s := by cases s; rfl

instance : Fintype E91State :=
  Fintype.ofEquiv (Context × Bit) equivProd

def key0 : E91State := ⟨Context.key, false⟩
def key1 : E91State := ⟨Context.key, true⟩
def test0 : E91State := ⟨Context.test, false⟩
def test1 : E91State := ⟨Context.test, true⟩

/-- Key-context states. -/
def keyStates : Set E91State :=
  {s | s.ctx = Context.key}

/-- Test-context states. -/
def testStates : Set E91State :=
  {s | s.ctx = Context.test}

/-- All states. -/
def allStates : Set E91State :=
  Set.univ

lemma key0_in_key : key0 ∈ keyStates := by simp [key0, keyStates]
lemma key1_in_key : key1 ∈ keyStates := by simp [key1, keyStates]
lemma test0_in_test : test0 ∈ testStates := by simp [test0, testStates]
lemma test1_in_test : test1 ∈ testStates := by simp [test1, testStates]

lemma union_is_all : keyStates ∪ testStates = allStates := by
  ext s
  cases s with
  | mk ctx bit =>
      cases ctx <;> simp [keyStates, testStates, allStates]

lemma contexts_disjoint : Disjoint keyStates testStates := by
  refine Set.disjoint_left.2 ?_
  intro s hk ht
  have hk' : s.ctx = Context.key := by simpa [keyStates] using hk
  have ht' : s.ctx = Context.test := by simpa [testStates] using ht
  exact Context.noConfusion (hk'.symm.trans ht')

lemma allStates_ne_keyStates : allStates ≠ keyStates := by
  intro h
  have : test0 ∈ keyStates := by
    have ht : test0 ∈ allStates := Set.mem_univ _
    simpa [h] using ht
  -- Note: avoid `unnecessarySimpa` linter warnings under `--wfail`.
  simp [keyStates, test0] at this

lemma allStates_ne_testStates : allStates ≠ testStates := by
  intro h
  have : key0 ∈ testStates := by
    have hk : key0 ∈ allStates := Set.mem_univ _
    simpa [h] using hk
  -- Note: avoid `unnecessarySimpa` linter warnings under `--wfail`.
  simp [testStates, key0] at this

end E91State

end E91
end QKD
end Crypto
end HeytingLean
