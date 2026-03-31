import HeytingLean.Meta.LeanTT0.Hash
import HeytingLean.Meta.LeanTT0.Rules
import HeytingLean.Meta.LeanTT0.Trace
import HeytingLean.Meta.LeanTT0.Core
import HeytingLean.Meta.LeanTT0.Merkle

namespace HeytingLean.Meta.LeanTT0

structure CAB where
  version : String := "cab-1"
  foundationCommitment : ByteArray
  rulesRoot : ByteArray

structure KernelInfo where
  kernelCommitment : ByteArray

structure Certificate where
  version : String := "cert-1"
  foundationCommitment : ByteArray
  rulesRoot : ByteArray
  kernelCommitment : ByteArray
  initialDigest : ByteArray
  finalDigest : ByteArray
  transcriptRoot : ByteArray

  /-- Deterministic replay + shallow validation checks. -/
  def replayAndVerify (cab : CAB) (ker : KernelInfo) (cert : Certificate) : Bool :=
    cab.rulesRoot == cert.rulesRoot &&
    cab.foundationCommitment == cert.foundationCommitment &&
    ker.kernelCommitment == cert.kernelCommitment &&
    cert.initialDigest != ByteArray.empty &&
    cert.finalDigest != ByteArray.empty

/-- Verify a β-only transcript against CAB rulesRoot by re-running semantics from `t0`. -/
def verifyTranscript (cab : CAB) (t0 : Tm) (tr : Transcript) : Bool := Id.run do
  if tr.initialDigest ≠ digestTerm t0 then return false
  let mut cur := t0
  for s in tr.steps do
    -- rule membership: single-leaf path (empty) accepted if rid.hash = rulesRoot
    let rid := ruleId s.rule
    if !verifyProof cab.rulesRoot rid.hash s.pathToRule then return false
    -- semantics: before digest matches
    if s.before ≠ digestTerm cur then return false
    match applyRule s.rule cur with
    | some nxt =>
        if s.after ≠ digestTerm nxt then return false
        cur := nxt
    | none => return false
  if tr.finalDigest ≠ digestTerm cur then return false
  true

end HeytingLean.Meta.LeanTT0
