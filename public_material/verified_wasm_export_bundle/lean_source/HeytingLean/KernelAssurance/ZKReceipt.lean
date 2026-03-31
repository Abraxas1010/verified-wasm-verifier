import Lean.Data.Json

namespace HeytingLean.KernelAssurance

open Lean

inductive AssuranceMode where
  | cab_only
  | cab_plus_zk_receipt
  deriving Repr, Inhabited, BEq, DecidableEq, ToJson, FromJson

instance : ToString AssuranceMode where
  toString
    | .cab_only => "cab_only"
    | .cab_plus_zk_receipt => "cab_plus_zk_receipt"

structure ZKReceiptMetadata where
  proofSystem : String
  circuitKind : String
  checkerDigest : String
  bundleDigest : String
  receiptDigest : String
  publicInputDigest : String
  verifierDigest : String
  executionClaim : String
  claimBoundary : String
  deriving Repr, Inhabited, BEq, ToJson, FromJson

def mkZKReceiptClaimBoundary (proofSystem checkerDigest bundleDigest : String) : String :=
  s!"Declared {proofSystem} receipt metadata is bound to the declared checker and bundle only " ++
  s!"(checkerDigest={checkerDigest}, bundleDigest={bundleDigest}); proof verification remains external to this Lean manifest, and it does not by itself prove Lean's full kernel."

def ZKReceiptMetadata.isConcrete (receipt : ZKReceiptMetadata) : Bool :=
  !(receipt.proofSystem.isEmpty ||
    receipt.checkerDigest.isEmpty ||
    receipt.bundleDigest.isEmpty ||
    receipt.receiptDigest.isEmpty ||
    receipt.publicInputDigest.isEmpty ||
    receipt.verifierDigest.isEmpty)

end HeytingLean.KernelAssurance
