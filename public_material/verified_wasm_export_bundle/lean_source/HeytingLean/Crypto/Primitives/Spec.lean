import HeytingLean.CCI.Core
import HeytingLean.Crypto.Commit.Spec
import HeytingLean.Crypto.Signature.Spec
import HeytingLean.Blockchain.MerkleModel
import HeytingLean.Crypto.Hash.Poseidon

/-
# Crypto.Primitives.Spec

Identifiers and metadata for cryptographic primitive properties (hashes,
signatures, encryption, commitments, and post-quantum primitives) from
sections 3 and 9 of `crypto_proofs_master_list.md`.
-/

namespace HeytingLean
namespace Crypto
namespace Primitives
namespace Spec

open HeytingLean.CCI

inductive PropertyId
  -- 3.1 Hash functions
  | keccak256Correctness
  | poseidonHashCorrectness
  | blake3Correctness
  | pedersenHashCorrectness
  | hashCollisionResistance
  -- 3.2 Signatures
  | ecdsaCorrectness
  | eddsaCorrectness
  | blsSignaturesCorrectness
  | schnorrSignaturesCorrectness
  | thresholdSignaturesCorrectness
  | multiSignaturesCorrectness
  -- 3.3 Encryption schemes
  | aesGcmCorrectness
  | chacha20Poly1305Correctness
  | eciesCorrectness
  | homomorphicEncryptionCorrectness
  -- 3.4 Commitments
  | pedersenCommitmentsSecurity
  | kzgCommitmentsCorrectness
  | merkleTreeProofsCorrectness
  | vectorCommitmentsCorrectness
  -- 9.1 Post-quantum signatures
  | dilithiumCorrectness
  | sphincsPlusCorrectness
  | falconCorrectness
  -- 9.2 Quantum-safe primitives
  | latticeEncryptionCorrectness
  | hashBasedCommitmentsPQ
  | starkQuantumSafety
  deriving DecidableEq, Repr

def PropertyId.slug : PropertyId → String
  | .keccak256Correctness        => "hash.keccak256_correctness"
  | .poseidonHashCorrectness     => "hash.poseidon_correctness"
  | .blake3Correctness           => "hash.blake3_correctness"
  | .pedersenHashCorrectness     => "hash.pedersen_correctness"
  | .hashCollisionResistance     => "hash.collision_resistance"
  | .ecdsaCorrectness            => "sig.ecdsa_correctness"
  | .eddsaCorrectness            => "sig.eddsa_correctness"
  | .blsSignaturesCorrectness    => "sig.bls_correctness"
  | .schnorrSignaturesCorrectness => "sig.schnorr_correctness"
  | .thresholdSignaturesCorrectness => "sig.threshold_correctness"
  | .multiSignaturesCorrectness  => "sig.multi_correctness"
  | .aesGcmCorrectness           => "enc.aes_gcm_correctness"
  | .chacha20Poly1305Correctness => "enc.chacha20_poly1305_correctness"
  | .eciesCorrectness            => "enc.ecies_correctness"
  | .homomorphicEncryptionCorrectness => "enc.homomorphic_correctness"
  | .pedersenCommitmentsSecurity => "commit.pedersen_security"
  | .kzgCommitmentsCorrectness   => "commit.kzg_correctness"
  | .merkleTreeProofsCorrectness => "commit.merkle_tree_proofs"
  | .vectorCommitmentsCorrectness => "commit.vector_commitments"
  | .dilithiumCorrectness        => "pq.sig.dilithium_correctness"
  | .sphincsPlusCorrectness      => "pq.sig.sphincs_plus_correctness"
  | .falconCorrectness           => "pq.sig.falcon_correctness"
  | .latticeEncryptionCorrectness => "pq.enc.lattice_encryption_correctness"
  | .hashBasedCommitmentsPQ      => "pq.commit.hash_based_commitments"
  | .starkQuantumSafety          => "pq.zk.stark_quantum_safety"

def PropertyId.title : PropertyId → String
  | .keccak256Correctness        => "Keccak-256 Correctness"
  | .poseidonHashCorrectness     => "Poseidon Hash Correctness"
  | .blake3Correctness           => "BLAKE3 Correctness"
  | .pedersenHashCorrectness     => "Pedersen Hash Correctness"
  | .hashCollisionResistance     => "Hash Collision Resistance"
  | .ecdsaCorrectness            => "ECDSA Correctness"
  | .eddsaCorrectness            => "EdDSA Correctness"
  | .blsSignaturesCorrectness    => "BLS Signatures"
  | .schnorrSignaturesCorrectness => "Schnorr Signatures"
  | .thresholdSignaturesCorrectness => "Threshold Signatures"
  | .multiSignaturesCorrectness  => "Multi-Signatures"
  | .aesGcmCorrectness           => "AES-GCM Correctness"
  | .chacha20Poly1305Correctness => "ChaCha20-Poly1305 Correctness"
  | .eciesCorrectness            => "ECIES Correctness"
  | .homomorphicEncryptionCorrectness => "Homomorphic Encryption"
  | .pedersenCommitmentsSecurity => "Pedersen Commitments"
  | .kzgCommitmentsCorrectness   => "Kate Commitments (KZG)"
  | .merkleTreeProofsCorrectness => "Merkle Tree Proofs"
  | .vectorCommitmentsCorrectness => "Vector Commitments"
  | .dilithiumCorrectness        => "Dilithium Correctness"
  | .sphincsPlusCorrectness      => "SPHINCS+ Correctness"
  | .falconCorrectness           => "Falcon Correctness"
  | .latticeEncryptionCorrectness => "Lattice Encryption"
  | .hashBasedCommitmentsPQ      => "Hash-Based Commitments (PQ)"
  | .starkQuantumSafety          => "STARK Quantum Safety"

def PropertyId.description : PropertyId → String
  | .keccak256Correctness =>
      "Implementation of Keccak-256 matches the published specification."
  | .poseidonHashCorrectness =>
      "Poseidon hash implementation matches the algebraic specification."
  | .blake3Correctness =>
      "BLAKE3 implementation is functionally correct with respect to its spec."
  | .pedersenHashCorrectness =>
      "Pedersen hash construction satisfies its correctness properties."
  | .hashCollisionResistance =>
      "Hash family satisfies collision resistance under standard assumptions."
  | .ecdsaCorrectness =>
      "ECDSA over secp256k1 (or other curves) is implemented correctly."
  | .eddsaCorrectness =>
      "EdDSA (e.g. Ed25519) signing and verification are correct."
  | .blsSignaturesCorrectness =>
      "BLS aggregate signatures verify correctly and support secure aggregation."
  | .schnorrSignaturesCorrectness =>
      "Schnorr-style signatures (e.g. Taproot) satisfy their correctness spec."
  | .thresholdSignaturesCorrectness =>
      "t-of-n threshold signature schemes produce valid, verifiable signatures."
  | .multiSignaturesCorrectness =>
      "Multi-signature schemes combine individual signatures correctly."
  | .aesGcmCorrectness =>
      "AES-GCM symmetric encryption and authentication are correct."
  | .chacha20Poly1305Correctness =>
      "ChaCha20-Poly1305 AEAD construction is correct."
  | .eciesCorrectness =>
      "ECIES-style public-key encryption satisfies its correctness guarantees."
  | .homomorphicEncryptionCorrectness =>
      "Homomorphic encryption operations preserve plaintext semantics."
  | .pedersenCommitmentsSecurity =>
      "Pedersen commitments are hiding and binding under standard assumptions."
  | .kzgCommitmentsCorrectness =>
      "Kate (KZG) polynomial commitments are correct and binding."
  | .merkleTreeProofsCorrectness =>
      "Merkle proof verification corresponds to membership in the Merkle tree."
  | .vectorCommitmentsCorrectness =>
      "Vector commitments are position binding and support correct openings."
  | .dilithiumCorrectness =>
      "Dilithium lattice-based signatures satisfy correctness properties."
  | .sphincsPlusCorrectness =>
      "SPHINCS+ hash-based signatures satisfy correctness properties."
  | .falconCorrectness =>
      "Falcon NTRU-based signatures satisfy correctness properties."
  | .latticeEncryptionCorrectness =>
      "CRYSTALS-Kyber and similar lattice encryption schemes are correct."
  | .hashBasedCommitmentsPQ =>
      "Hash-based commitments remain secure in the post-quantum setting."
  | .starkQuantumSafety =>
      "STARK protocols retain security against quantum adversaries."

def PropertyId.toExpr (p : PropertyId) : Expr :=
  Expr.atom p.slug

/-- Specification-level statement for a simple string-based commitment
    scheme: for any fixed domain tag, the scheme instantiated by
    `commitString` satisfies the generic `Scheme.Correct` property. This
    serves as a minimal, fully proved commitment-correctness instance
    aligned with commitment-related `PropertyId`s. -/
def StringCommitmentCorrectnessStatement (domain : String) : Prop :=
  Commit.Spec.Scheme.Correct (Commit.Spec.StringScheme domain)

/-- `StringCommitmentCorrectnessStatement` holds for every domain,
    witnessed by the correctness theorem in `Crypto.Commit.Spec`. -/
theorem stringCommitmentCorrectnessStatement_holds (domain : String) :
    StringCommitmentCorrectnessStatement domain :=
  Commit.Spec.StringScheme_correct domain

/-- Specification-level correctness statement for the example signature
    scheme from `Crypto.Signature.Spec`: it satisfies the generic
    `Scheme.Correct` property. This serves as a minimal, fully proved
    signature-correctness instance aligned with the signature-related
    `PropertyId`s, while real ECDSA/EdDSA/BLS/etc. remain blueprint. -/
def DemoSignatureCorrectnessStatement : Prop :=
  Signature.Spec.Scheme.Correct Signature.Spec.demoScheme

/-- `DemoSignatureCorrectnessStatement` holds, witnessed by the
    correctness theorem in `Crypto.Signature.Spec`. -/
theorem demoSignatureCorrectnessStatement_holds :
    DemoSignatureCorrectnessStatement :=
  Signature.Spec.demoScheme_correct

/-- Specification-level correctness statement for Merkle tree proofs:
    whenever the structural search `Blockchain.MerkleModel.buildPath?`
    finds a path for a payload `x` in a tree `t`, the pure
    `verifyMembership` helper accepts the corresponding proof and
    reproduces the structural root. This is a direct realisation of
    `PropertyId.merkleTreeProofsCorrectness` at the primitives level. -/
def MerkleTreeProofsCorrectnessStatement : Prop :=
  ∀ (x : String) (t : Blockchain.MerkleModel.Tree) (path : List HeytingLean.Payments.Merkle.PathElem),
    Blockchain.MerkleModel.buildPath? x t = some path →
      HeytingLean.Payments.Merkle.verifyMembership
          ({ root := Blockchain.MerkleModel.root t
             recipient := x
             path := path } :
            HeytingLean.Payments.Merkle.VProof) =
        (true, Blockchain.MerkleModel.root t)

/-- `MerkleTreeProofsCorrectnessStatement` holds, witnessed by the
    structural correctness theorem in `Blockchain.MerkleModel`. -/
theorem merkleTreeProofsCorrectnessStatement_holds :
    MerkleTreeProofsCorrectnessStatement := by
  intro x t path h
  exact Blockchain.MerkleModel.verifyMembership_of_buildPath? x t path h

/-- Abstract KZG-style polynomial-commitment correctness statement:
    for any polynomial commitment scheme `S`, the evaluation-correctness
    and evaluation-soundness properties hold. This is deliberately
    scheme-agnostic: concrete KZG-style instances can instantiate
    `Poly.Scheme` and then prove this bundled property. -/
def PolyCommitmentCorrectnessStatement
    (S : Commit.Spec.Poly.Scheme) : Prop :=
  Commit.Spec.Poly.Scheme.EvalCorrect S ∧
    Commit.Spec.Poly.Scheme.EvalSound S

/-- Specification-level correctness statement for the example polynomial
    commitment scheme `Commit.Spec.Poly.demoScheme`. This witnesses the
    bundled `PolyCommitmentCorrectnessStatement` for a minimal,
    non-cryptographic instance, providing a concrete, fully proved
    polynomial-commitment correctness example at the primitives level. -/
def DemoPolyCommitmentCorrectnessStatement : Prop :=
  PolyCommitmentCorrectnessStatement Commit.Spec.Poly.demoScheme

/-- `DemoPolyCommitmentCorrectnessStatement` holds, witnessed directly
    by the evaluation correctness and soundness lemmas for
    `Commit.Spec.Poly.demoScheme`. -/
theorem demoPolyCommitmentCorrectnessStatement_holds :
    DemoPolyCommitmentCorrectnessStatement :=
  And.intro Commit.Spec.Poly.demoScheme_evalCorrect
            Commit.Spec.Poly.demoScheme_evalSound

/-- Abstract vector-commitment correctness statement: for any vector
    commitment scheme `S`, the opening-correctness and opening-soundness
    properties hold. As with the polynomial case, this is agnostic to
    concrete constructions. -/
def VectorCommitmentCorrectnessStatement
    (S : Commit.Spec.Vec.Scheme) : Prop :=
  Commit.Spec.Vec.Scheme.OpenCorrect S ∧
    Commit.Spec.Vec.Scheme.OpenSound S

/-- Specification-level correctness statement for the example vector
    commitment scheme `Commit.Spec.Vec.demoScheme`. This provides a
    minimal, fully proved vector-commitment correctness example at the
    primitives level. -/
def DemoVectorCommitmentCorrectnessStatement : Prop :=
  VectorCommitmentCorrectnessStatement Commit.Spec.Vec.demoScheme

/-- `DemoVectorCommitmentCorrectnessStatement` holds, witnessed by the
    opening correctness and soundness lemmas for
    `Commit.Spec.Vec.demoScheme`. -/
theorem demoVectorCommitmentCorrectnessStatement_holds :
    DemoVectorCommitmentCorrectnessStatement :=
  And.intro Commit.Spec.Vec.demoScheme_openCorrect
            Commit.Spec.Vec.demoScheme_openSound

/-- Specification-level statement for the current Poseidon hash
    boundary: `poseidonCommit` is implemented as a domain-separated
    wrapper around `commitString` with prefix `"POSEIDON:<domain>"`. -/
def PoseidonHashCorrectnessStatement : Prop :=
  ∀ (domain payload : String),
    Crypto.Hash.poseidonCommit domain payload =
      Crypto.commitString (s!"POSEIDON:{domain}") payload

/-- `PoseidonHashCorrectnessStatement` holds definitionally, since
    `poseidonCommit` is currently defined in terms of `commitString`
    with the appropriate domain-separation prefix. -/
theorem poseidonHashCorrectnessStatement_holds :
    PoseidonHashCorrectnessStatement := by
  intro domain payload
  rfl

end Spec
end Primitives
end Crypto
end HeytingLean
