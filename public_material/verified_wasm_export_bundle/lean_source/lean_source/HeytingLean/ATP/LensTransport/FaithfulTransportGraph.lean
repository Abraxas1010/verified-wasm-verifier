import HeytingLean.ATP.DifferentiableATP.SheafResolution
import HeytingLean.ATP.DifferentiableATP.SheafTransport
import HeytingLean.Embeddings.CrossLensTransport

/-
- source_type: infrastructure (audit encoding)
- attribution_status: n/a
- claim_status: n/a
- proof_status: proved
-/

namespace HeytingLean
namespace ATP
namespace LensTransport

open HeytingLean.Embeddings

/-- Canonical finite carrier for lens graph traversals. -/
def allLenses : List LensID :=
  [.omega, .tensor, .graph, .clifford, .topology, .region, .matula]

/-- Decidable `basisSubset` view used by runtime graph queries. -/
def basisSubsetB (fine coarse : LensID) : Bool :=
  (DifferentiableATP.basisForLens coarse).all (fun c =>
    c ∈ DifferentiableATP.basisForLens fine)

theorem basisSubsetB_eq_true_iff (fine coarse : LensID) :
    basisSubsetB fine coarse = true ↔ DifferentiableATP.basisSubset fine coarse := by
  unfold basisSubsetB DifferentiableATP.basisSubset
  simp

/-- Classification of transport faithfulness between two lenses. -/
inductive TransportClass where
  /-- Full isomorphism: RT-1 + RT-2, zero information loss. -/
  | iso
  /-- `src → dst` is a retraction (`basisSubset src dst`): fine to coarse. -/
  | retract
  /-- `src → dst` is an expansion (`basisSubset dst src`): coarse to fine. -/
  | expansion
  /-- Incomparable: transport is not faithful. -/
  | incomparable
  /-- Unknown relationship. -/
  | unknown
  deriving DecidableEq, Repr

/-- Query the transport class between two `LensID` values. -/
def transportClass : LensID → LensID → TransportClass
  | src, dst =>
      if src == dst then
        .iso
      else if basisSubsetB src dst then
        .retract
      else if basisSubsetB dst src then
        .expansion
      else
        .incomparable

/-- The set of lenses reachable from `src` via safe transport. -/
def faithfulTargets (src : LensID) : List LensID :=
  allLenses.filter (fun dst => basisSubsetB src dst)

/-- Check whether `src → dst` is safe for proof search transitions.
    Safe means retract/identity (`basisSubset src dst`), so proof candidates
    found in `dst` can be expanded back to `src` without truncation. -/
def isSafeTransport (src dst : LensID) : Bool :=
  basisSubsetB src dst

theorem isSafeTransport_iff_basisSubset (src dst : LensID) :
    isSafeTransport src dst = true ↔ DifferentiableATP.basisSubset src dst := by
  simpa [isSafeTransport] using basisSubsetB_eq_true_iff src dst

theorem transportClass_retract_iff (src dst : LensID) :
    transportClass src dst = .retract ↔
      src ≠ dst ∧ DifferentiableATP.basisSubset src dst := by
  by_cases hEq : src = dst
  · subst hEq
    simp [transportClass]
  · by_cases hSub : basisSubsetB src dst = true
    · have hSubProp : DifferentiableATP.basisSubset src dst :=
        (basisSubsetB_eq_true_iff src dst).1 hSub
      simp [transportClass, hEq, hSub, hSubProp]
    · have hNotSubProp : ¬ DifferentiableATP.basisSubset src dst := by
        intro hs
        exact hSub ((basisSubsetB_eq_true_iff src dst).2 hs)
      by_cases hRev : basisSubsetB dst src = true
      · simp [transportClass, hEq, hSub, hRev, hNotSubProp]
      · simp [transportClass, hEq, hSub, hRev, hNotSubProp]

/-- Self-transport is always safe. -/
theorem isSafeTransport_refl (l : LensID) :
    isSafeTransport l l = true := by
  cases l <;> native_decide

/-- omega can reach every other lens safely. -/
theorem omega_reaches_all (dst : LensID) :
    isSafeTransport .omega dst = true := by
  cases dst <;> native_decide

theorem region_reaches_only_self (dst : LensID) :
    isSafeTransport .region dst = decide (dst = .region) := by
  cases dst <;> native_decide

/-- Incomparable transports are never safe. -/
theorem graph_tensor_unsafe :
    isSafeTransport .graph .tensor = false := by
  native_decide

theorem clifford_topology_unsafe :
    isSafeTransport .clifford .topology = false := by
  native_decide

end LensTransport
end ATP
end HeytingLean
