/-
  Certified Axiom Bundle (CAB): cryptographic commitment to proofs.

  The CAB carries:
  - an executable artifact (runtime value),
  - a specification proof (erased),
  - a proof commitment (hash over external proof bytes),
  - metadata (fragment/dimension/lens tags).
-/

import HeytingLean.Certified.Basic
import HeytingLean.Erasure.Fragment
import HeytingLean.Lens.Certified
import HeytingLean.Util.SHA

namespace HeytingLean

namespace CAB

universe u

/-- Dimension classification (Heyting/Quantum/Classical/Modal). -/
inductive Dimension
  | D1  -- Heyting (intuitionistic)
  | D2  -- Quantum (superposition)
  | D3  -- Classical (boolean)
  | D4  -- Modal (necessity/possibility)
deriving DecidableEq, Repr

/-- Cryptographic hash of a proof (for commitment). -/
structure ProofHash where
  hash : ByteArray
  algorithm : String := "SHA256"

/-- CAB metadata. -/
structure CABMetadata where
  fragment : HeytingLean.Erasure.FragmentId
  dimension : Dimension
  lensCompatibility : List HeytingLean.Lens.LensId
  timestamp : Nat
deriving Repr

end CAB

open HeytingLean.Certified

/-- Certified Axiom Bundle. -/
structure CAB (α : Type u) (Spec : α → Prop) where
  /-- The executable artifact. -/
  artifact : α
  /-- The specification it satisfies (erased). -/
  spec : Spec artifact
  /-- Commitment to the proof (without carrying full proof). -/
  proofCommitment : CAB.ProofHash
  /-- Classification metadata. -/
  metadata : CAB.CABMetadata

namespace CAB

/-- Extract artifact for compilation. -/
@[inline] def extract {α : Type u} {Spec : α → Prop} (cab : HeytingLean.CAB α Spec) : α :=
  cab.artifact

/-- Verify CAB against a proof (offline verification by hash check). -/
def verify {α : Type u} {Spec : α → Prop} (cab : HeytingLean.CAB α Spec) (proofBytes : ByteArray) : Bool :=
  decide (HeytingLean.Util.SHA256.sha256Bytes proofBytes = cab.proofCommitment.hash)

/-- Create CAB from a `Certified` value (caller supplies a commitment function). -/
def fromCertified {α : Type u} {Spec : α → Prop}
    (c : Certified α Spec)
    (computeHash : Spec c.val → ProofHash)
    (md : CABMetadata) : HeytingLean.CAB α Spec :=
  ⟨c.val, c.ok, computeHash c.ok, md⟩

end CAB

end HeytingLean
