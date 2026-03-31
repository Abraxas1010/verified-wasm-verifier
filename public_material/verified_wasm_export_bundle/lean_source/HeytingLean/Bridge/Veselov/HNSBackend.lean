import Mathlib.Data.Finset.Basic

/-!
# Bridge.Veselov.HNSBackend

Constructive HNS bridge surface:
- finite-support backend carrier,
- exact encode/decode,
- meet/join precision-preservation theorems.
-/

namespace HeytingLean.Bridge.Veselov

/-- HNS backend value carrier (finite support view). -/
abbrev HNSValue : Type := Finset Nat

/-- Backend encoding (lossless in this formal lane). -/
def hnsEncode (s : Finset Nat) : HNSValue := s

/-- Backend decoding (lossless in this formal lane). -/
def hnsDecode (h : HNSValue) : Finset Nat := h

/-- HNS meet operation. -/
def hnsMeet (a b : HNSValue) : HNSValue := a ∩ b

/-- HNS join operation. -/
def hnsJoin (a b : HNSValue) : HNSValue := a ∪ b

@[simp] theorem hns_roundtrip_left (s : Finset Nat) :
    hnsDecode (hnsEncode s) = s := rfl

@[simp] theorem hns_roundtrip_right (h : HNSValue) :
    hnsEncode (hnsDecode h) = h := rfl

@[simp] theorem hns_meet_precision (a b : Finset Nat) :
    hnsDecode (hnsMeet (hnsEncode a) (hnsEncode b)) = a ∩ b := rfl

@[simp] theorem hns_join_precision (a b : Finset Nat) :
    hnsDecode (hnsJoin (hnsEncode a) (hnsEncode b)) = a ∪ b := rfl

/-- T3.5 packaged theorem: lattice operations are represented with zero precision loss. -/
theorem hns_precision_preservation (a b : Finset Nat) :
    hnsDecode (hnsMeet (hnsEncode a) (hnsEncode b)) = a ∩ b ∧
    hnsDecode (hnsJoin (hnsEncode a) (hnsEncode b)) = a ∪ b := by
  constructor <;> rfl

/-- External backend trace payload used for surrogate-parity checks. -/
structure ExternalHNSTrace where
  leftInput : Finset Nat
  rightInput : Finset Nat
  meetOutput : Finset Nat
  joinOutput : Finset Nat
  backendTag : String
  provenanceHash : String

/-- Adapter boundary for plugging external HNS backends into the parity contract lane. -/
structure ExternalHNSBackendAdapter where
  backendTag : String
  provenanceHash : String
  runMeet : Finset Nat → Finset Nat → Finset Nat
  runJoin : Finset Nat → Finset Nat → Finset Nat

/-- Deterministic trace builder from an external adapter invocation. -/
def adapterTrace (A : ExternalHNSBackendAdapter) (left right : Finset Nat) : ExternalHNSTrace where
  leftInput := left
  rightInput := right
  meetOutput := A.runMeet left right
  joinOutput := A.runJoin left right
  backendTag := A.backendTag
  provenanceHash := A.provenanceHash

/-- Meet-parity predicate between external output and formal surrogate. -/
def traceMeetParity (T : ExternalHNSTrace) : Prop :=
  T.meetOutput = T.leftInput ∩ T.rightInput

/-- Join-parity predicate between external output and formal surrogate. -/
def traceJoinParity (T : ExternalHNSTrace) : Prop :=
  T.joinOutput = T.leftInput ∪ T.rightInput

/-- Full parity contract for one external trace item. -/
def traceParity (T : ExternalHNSTrace) : Prop :=
  traceMeetParity T ∧ traceJoinParity T

/-- Decidable pass/fail view suitable for CLI validators. -/
noncomputable def traceParityCheck (T : ExternalHNSTrace) : Bool := by
  classical
  exact decide (traceParity T)

theorem traceParityCheck_eq_true_iff (T : ExternalHNSTrace) :
    traceParityCheck T = true ↔ traceParity T := by
  classical
  simp [traceParityCheck, traceParity]

theorem traceParity_of_outputs (T : ExternalHNSTrace)
    (hmeet : T.meetOutput = T.leftInput ∩ T.rightInput)
    (hjoin : T.joinOutput = T.leftInput ∪ T.rightInput) :
    traceParity T := ⟨hmeet, hjoin⟩

theorem adapterTrace_meetParity (A : ExternalHNSBackendAdapter) (left right : Finset Nat)
    (hmeet : A.runMeet left right = left ∩ right) :
    traceMeetParity (adapterTrace A left right) := by
  exact hmeet

theorem adapterTrace_joinParity (A : ExternalHNSBackendAdapter) (left right : Finset Nat)
    (hjoin : A.runJoin left right = left ∪ right) :
    traceJoinParity (adapterTrace A left right) := by
  exact hjoin

theorem adapterTrace_fullParity (A : ExternalHNSBackendAdapter) (left right : Finset Nat)
    (hmeet : A.runMeet left right = left ∩ right)
    (hjoin : A.runJoin left right = left ∪ right) :
    traceParity (adapterTrace A left right) := by
  exact ⟨adapterTrace_meetParity A left right hmeet, adapterTrace_joinParity A left right hjoin⟩

theorem traceParity_join_sound (T : ExternalHNSTrace) (h : traceParity T) :
    hnsDecode (hnsJoin (hnsEncode T.leftInput) (hnsEncode T.rightInput)) = T.joinOutput := by
  rcases h with ⟨_, hjoin⟩
  calc
    hnsDecode (hnsJoin (hnsEncode T.leftInput) (hnsEncode T.rightInput))
        = T.leftInput ∪ T.rightInput := by
          rfl
    _ = T.joinOutput := by
      exact hjoin.symm

theorem traceParity_meet_sound (T : ExternalHNSTrace) (h : traceParity T) :
    hnsDecode (hnsMeet (hnsEncode T.leftInput) (hnsEncode T.rightInput)) = T.meetOutput := by
  rcases h with ⟨hmeet, _⟩
  calc
    hnsDecode (hnsMeet (hnsEncode T.leftInput) (hnsEncode T.rightInput))
        = T.leftInput ∩ T.rightInput := by
          rfl
    _ = T.meetOutput := by
      exact hmeet.symm

end HeytingLean.Bridge.Veselov
