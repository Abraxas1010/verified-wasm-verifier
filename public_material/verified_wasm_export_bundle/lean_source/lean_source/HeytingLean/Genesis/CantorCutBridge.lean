import HeytingLean.Genesis.Observer
import HeytingLean.Genesis.WitnessInterior

/-!
# Genesis.CantorCutBridge

Phase-9 bridge from Cantor-cut evaluation paths into post-re-entry witness
interior objects.
-/

namespace HeytingLean.Genesis

open CoGame

/-- A path-indexed source classifier using the head bit as strict/permissive seed. -/
def headWitnessSource (p : EvalPath) : CoGame :=
  if p 0 then CoGame.Void else CoGame.Life

@[simp] theorem headWitnessSource_true {p : EvalPath} (h : p 0 = true) :
    headWitnessSource p = CoGame.Void := by
  simp [headWitnessSource, h]

@[simp] theorem headWitnessSource_false {p : EvalPath} (h : p 0 = false) :
    headWitnessSource p = CoGame.Life := by
  simp [headWitnessSource, h]

/-- Stabilization classification for path-driven witness sources. -/
theorem headWitnessSource_eventualStabilizes_iff (p : EvalPath) :
    eventualStabilizes (headWitnessSource p) ↔ p 0 = true := by
  cases h0 : p 0 with
  | false =>
      simp [headWitnessSource, h0, life_not_eventualStabilizes]
  | true =>
      simp [headWitnessSource, h0, void_eventualStabilizes]

/-- Canonical Cantor-cut to witness-interior lift (depth is post-re-entry by construction). -/
def cantorCut_to_witnessInterior (p : EvalPath) (depth : Nat) : WitnessInterior where
  source := headWitnessSource p
  depth := depth.succ
  postReentry := Nat.succ_pos depth

@[simp] theorem cantorCut_to_witnessInterior_source (p : EvalPath) (depth : Nat) :
    (cantorCut_to_witnessInterior p depth).source = headWitnessSource p := rfl

@[simp] theorem cantorCut_to_witnessInterior_depth (p : EvalPath) (depth : Nat) :
    (cantorCut_to_witnessInterior p depth).depth = depth.succ := rfl

/-- Transport readiness criterion for path-lifted witness interiors. -/
theorem cantorCut_transport_ready (p : EvalPath) (depth : Nat) :
    eventualStabilizes (cantorCut_to_witnessInterior p depth).source ↔ p 0 = true := by
  simpa [cantorCut_to_witnessInterior] using headWitnessSource_eventualStabilizes_iff p

end HeytingLean.Genesis

