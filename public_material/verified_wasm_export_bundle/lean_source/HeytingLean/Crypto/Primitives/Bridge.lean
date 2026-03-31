import HeytingLean.Crypto.Primitives.Spec

/-
# Crypto.Primitives.Bridge

Registry-style bridge from `Crypto.Primitives.Spec.PropertyId` to
spec-level statements over primitives. This mirrors the pattern used in
other domains (e.g. DeFiBridge, Governance.Bridge): we keep a lightweight
`propertyHolds` function together with small witness lemmas.

For now we give a concrete meaning only to the Merkle-tree proofs row;
other primitive rows remain `True` defaults until more detailed
models are added. -/

namespace HeytingLean
namespace Crypto
namespace Primitives
namespace Bridge

open HeytingLean.Crypto.Primitives

/-- Interpretation of `Crypto.Primitives.Spec.PropertyId` at the
    primitives-spec level. Currently:

* `merkleTreeProofsCorrectness` is mapped to
  `MerkleTreeProofsCorrectnessStatement`;
* `poseidonHashCorrectness` is mapped to
  `PoseidonHashCorrectnessStatement`, capturing the current boundary
  semantics that `poseidonCommit` is a domain-separated wrapper around
  `commitString`;
* `kzgCommitmentsCorrectness` is mapped to the bundled example
  polynomial-commitment correctness statement
  `DemoPolyCommitmentCorrectnessStatement`; and
* `vectorCommitmentsCorrectness` is mapped to the bundled example
  vector-commitment correctness statement
  `DemoVectorCommitmentCorrectnessStatement`.

All other rows are left as `True` defaults to be refined when
concrete models and statements are introduced. -/
def propertyHolds (p : Spec.PropertyId) : Prop :=
  match p with
  | .merkleTreeProofsCorrectness =>
      Spec.MerkleTreeProofsCorrectnessStatement
  | .keccak256Correctness        => True
  | .poseidonHashCorrectness     => Spec.PoseidonHashCorrectnessStatement
  | .blake3Correctness           => True
  | .pedersenHashCorrectness     => True
  | .hashCollisionResistance     => True
  | .ecdsaCorrectness            => True
  | .eddsaCorrectness            => True
  | .blsSignaturesCorrectness    => True
  | .schnorrSignaturesCorrectness => True
  | .thresholdSignaturesCorrectness => True
  | .multiSignaturesCorrectness  => True
  | .aesGcmCorrectness           => True
  | .chacha20Poly1305Correctness => True
  | .eciesCorrectness            => True
  | .homomorphicEncryptionCorrectness => True
  | .pedersenCommitmentsSecurity => True
  | .kzgCommitmentsCorrectness   =>
      Spec.DemoPolyCommitmentCorrectnessStatement
  | .vectorCommitmentsCorrectness =>
      Spec.DemoVectorCommitmentCorrectnessStatement
  | .dilithiumCorrectness        => True
  | .sphincsPlusCorrectness      => True
  | .falconCorrectness           => True
  | .latticeEncryptionCorrectness => True
  | .hashBasedCommitmentsPQ      => True
  | .starkQuantumSafety          => True

/-- For the Poseidon-hash correctness row, the bridge maps to the
    definitional statement that `poseidonCommit` is implemented via
    a domain-separated `commitString`. -/
theorem propertyHolds_poseidonHashCorrectness :
    propertyHolds Spec.PropertyId.poseidonHashCorrectness := by
  -- This reduces to the primitives-level Poseidon correctness lemma.
  simpa [propertyHolds] using Spec.poseidonHashCorrectnessStatement_holds

/-- For the KZG-style polynomial-commitment correctness row, the bridge
    is currently realised by the example polynomial commitment scheme:
    `DemoPolyCommitmentCorrectnessStatement` bundles evaluation
    correctness and soundness for `Commit.Spec.Poly.demoScheme`. -/
theorem propertyHolds_kzgCommitmentsCorrectness :
    propertyHolds Spec.PropertyId.kzgCommitmentsCorrectness := by
  simpa [propertyHolds] using
    Spec.demoPolyCommitmentCorrectnessStatement_holds

/-- For the vector-commitment correctness row, the bridge is currently
    realised by the example vector commitment scheme:
    `DemoVectorCommitmentCorrectnessStatement` bundles opening
    correctness and soundness for `Commit.Spec.Vec.demoScheme`. -/
theorem propertyHolds_vectorCommitmentsCorrectness :
    propertyHolds Spec.PropertyId.vectorCommitmentsCorrectness := by
  simpa [propertyHolds] using
    Spec.demoVectorCommitmentCorrectnessStatement_holds

/-- For the Merkle-tree proofs correctness row, the bridge maps
    directly to `MerkleTreeProofsCorrectnessStatement`, which is
    witnessed by `merkleTreeProofsCorrectnessStatement_holds`. -/
theorem propertyHolds_merkleTreeProofs :
    propertyHolds Spec.PropertyId.merkleTreeProofsCorrectness := by
  -- By unfolding `propertyHolds`, this reduces to the primitives-level
  -- correctness theorem for Merkle tree proofs.
  simpa [propertyHolds] using Spec.merkleTreeProofsCorrectnessStatement_holds

end Bridge
end Primitives
end Crypto
end HeytingLean
