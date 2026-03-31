import HeytingLean.CAB.Compile

/-!
# CAB.Verified

Soundness-facing helper lemmas for CAB hash verification.
-/

namespace HeytingLean
namespace CAB

/-- Boolean CAB verification is exactly hash equality against the commitment. -/
theorem verify_eq_true_iff
    {α : Type _} {Spec : α → Prop}
    (cab : HeytingLean.CAB α Spec)
    (proofBytes : ByteArray) :
    CAB.verify cab proofBytes = true
      ↔ HeytingLean.Util.SHA256.sha256Bytes proofBytes = cab.proofCommitment.hash := by
  unfold CAB.verify
  exact decide_eq_true_iff

/-- Soundness form: a successful CAB verification certifies commitment-hash equality. -/
theorem verify_sound
    {α : Type _} {Spec : α → Prop}
    (cab : HeytingLean.CAB α Spec)
    (proofBytes : ByteArray)
    (h : CAB.verify cab proofBytes = true) :
    HeytingLean.Util.SHA256.sha256Bytes proofBytes = cab.proofCommitment.hash :=
  (verify_eq_true_iff cab proofBytes).mp h

end CAB
end HeytingLean
