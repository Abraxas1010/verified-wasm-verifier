import HeytingLean.CAB.Certified
import HeytingLean.CAB.Verified
import HeytingLean.LeanSP.Lang.YulSyntax

/-!
# LeanSP.Pipeline.CABExport

Integrates LeanSP verification results with the existing HeytingLean.CAB pipeline.
Creates actual `HeytingLean.CAB` values from verified Solidity contracts.
-/

namespace LeanSP.Pipeline

open HeytingLean

/-- Solidity-specific CAB metadata. -/
structure SolidityCABMeta where
  solSourceHash    : String
  yulHash          : String
  bytecodeHash     : String
  verificationTier : Nat
  provedProperties : Array String
  deriving Repr, Inhabited

inductive VerificationTier where
  | arithmetic | storage | full
  deriving Repr, BEq

def VerificationTier.toNat : VerificationTier → Nat
  | .arithmetic => 1 | .storage => 2 | .full => 3

def buildSolidityMeta (solHash yulHash bcHash : String)
    (tier : VerificationTier) (properties : Array String) : SolidityCABMeta :=
  { solSourceHash := solHash, yulHash := yulHash, bytecodeHash := bcHash,
    verificationTier := tier.toNat, provedProperties := properties }

/-- Create an actual HeytingLean.CAB from a verified Solidity contract.
    Wires through the existing CAB pipeline (fromCertified → CAB). -/
def mkSolidityCAB
    (cabMeta : SolidityCABMeta)
    (spec : SolidityCABMeta → Prop)
    (proof : spec cabMeta)
    (proofBytes : ByteArray)
    (timestamp : Nat) : HeytingLean.CAB SolidityCABMeta spec :=
  CAB.fromCertified
    (Certified.Certified.mk cabMeta proof)
    (fun _ => ⟨Util.SHA256.sha256Bytes proofBytes, "SHA256"⟩)
    { fragment := .Custom "solidity"
      dimension := .D3
      lensCompatibility := []
      timestamp := timestamp }

/-- Verify a CAB's proof commitment against provided proof bytes. -/
def verifySolidityCAB
    {spec : SolidityCABMeta → Prop}
    (cab : HeytingLean.CAB SolidityCABMeta spec)
    (proofBytes : ByteArray) : Bool :=
  CAB.verify cab proofBytes

/-- Extract the verified artifact from a CAB. -/
def extractCabMeta
    {spec : SolidityCABMeta → Prop}
    (cab : HeytingLean.CAB SolidityCABMeta spec) : SolidityCABMeta :=
  CAB.extract cab

/-- CAB verification soundness: if verify returns true,
    proof bytes match the commitment hash. -/
theorem verifySolidityCAB_sound
    {spec : SolidityCABMeta → Prop}
    (cab : HeytingLean.CAB SolidityCABMeta spec)
    (proofBytes : ByteArray)
    (h : verifySolidityCAB cab proofBytes = true) :
    Util.SHA256.sha256Bytes proofBytes = cab.proofCommitment.hash := by
  unfold verifySolidityCAB at h
  exact (CAB.verify_eq_true_iff cab proofBytes).mp h

end LeanSP.Pipeline
