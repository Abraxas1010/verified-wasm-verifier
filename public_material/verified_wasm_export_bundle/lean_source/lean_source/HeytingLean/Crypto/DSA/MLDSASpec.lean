import HeytingLean.Crypto.DSA.MLDSA204Params
import Mathlib.Data.ZMod.Basic

/-!
# ML-DSA (FIPS 204) spec interface (no placeholders, no axioms)

This repository currently contains:
- `HeytingLean.Crypto.DSA.MLDSA` (a toy, executable sign/open skeleton for plumbing); and
- `HeytingLean.Crypto.DSA.MLDSA204Params` (FIPS 204 parameter bookkeeping for ML-DSA-44/65/87).

The *full* ML-DSA spec is a larger project (hash/XOF expansion, NTT-domain arithmetic, rejection
sampling with aborts, hints). To keep the codebase policy-compliant, this file defines a **spec
interface** that future implementations can satisfy without introducing placeholder proofs.

References:
- NIST FIPS 204 (ML-DSA): https://nvlpubs.nist.gov/nistpubs/fips/nist.fips.204.pdf
- CRYPTO 2023 / Formosa Crypto: formal security proof structure for Dilithium-like schemes
  (Fiat–Shamir with aborts): https://eprint.iacr.org/2023/246
-/

namespace HeytingLean
namespace Crypto
namespace DSA
namespace FIPS204

variable (p : MLDSA204Params)

/-- Coefficient carrier for the FIPS 204 prime modulus. -/
abbrev Coeff (p : MLDSA204Params) : Type := ZMod p.q

/-- Spec-level polynomial carrier with `n` coefficients. -/
abbrev Poly (p : MLDSA204Params) : Type := Fin p.n → Coeff p

/-- Spec-level vector of polynomials of length `m`. -/
abbrev PolyVec (p : MLDSA204Params) (m : Nat) : Type := Fin m → Poly p

/-- Spec-level public key carrier (opaque to this layer). -/
structure PublicKey (_p : MLDSA204Params) where
  bytes : ByteArray

/-- Spec-level secret key carrier (opaque to this layer). -/
structure SecretKey (_p : MLDSA204Params) where
  bytes : ByteArray

/-- Spec-level signature carrier (opaque to this layer). -/
structure Signature (_p : MLDSA204Params) where
  bytes : ByteArray

/-- Parameter-indexed public-key view used by the native spec layer. -/
structure PublicKeyRepr (p : MLDSA204Params) where
  rho : ByteArray
  t1 : PolyVec p p.k

/-- Parameter-indexed secret-key view used by the native spec layer. -/
structure SecretKeyRepr (p : MLDSA204Params) where
  rho : ByteArray
  key : ByteArray
  tr : ByteArray
  s1 : PolyVec p p.ℓ
  s2 : PolyVec p p.k
  t0 : PolyVec p p.k

/-- Parameter-indexed signature view used by the native spec layer. -/
structure SignatureRepr (p : MLDSA204Params) where
  challengeSeed : ByteArray
  z : PolyVec p p.ℓ
  hintWeight : Nat

/-- Explicit sign result, preserving Fiat-Shamir-with-aborts behavior. -/
structure SigningResult (p : MLDSA204Params) where
  attemptSeed : ByteArray
  signature? : Option (Signature p)
  aborted : Bool
  aborts_exact : aborted = signature?.isNone

/-- Well-formedness of the sign result with respect to its abort flag. -/
def SigningResult.accepts (result : SigningResult p) : Prop :=
  match result.signature? with
  | some _ => result.aborted = false
  | none => result.aborted = true

/-- A spec interface for ML-DSA at parameter set `p`. -/
structure Spec where
  /-- Key generation from a seed (spec-level, deterministic). -/
  keygen : ByteArray → PublicKey p × SecretKey p
  /-- Structured parameter-indexed views for the opaque carriers. -/
  pkRepr : PublicKey p → PublicKeyRepr p
  skRepr : SecretKey p → SecretKeyRepr p
  sigRepr : Signature p → SignatureRepr p
  /-- Signing may abort; the result records that fact explicitly. -/
  sign : SecretKey p → ByteArray → SigningResult p
  /-- Verification is total. -/
  verify : PublicKey p → ByteArray → Signature p → Bool
  /-- Key generation preserves the shared public seed. -/
  keygen_rho_matches :
    ∀ seed, (pkRepr (keygen seed).1).rho = (skRepr (keygen seed).2).rho
  /-- Verified signatures satisfy the parameter-indexed hint bound. -/
  verify_hint_bound :
    ∀ (pk : PublicKey p) (msg : ByteArray) (σ : Signature p),
      verify pk msg σ = true →
      (sigRepr σ).hintWeight ≤ p.ω

  /-- Correctness: signatures produced by `sign` verify. -/
  verify_sign :
    ∀ (seed msg : ByteArray) (pk : PublicKey p) (sk : SecretKey p) (result : SigningResult p),
      keygen seed = (pk, sk) →
      sign sk msg = result →
      match result.signature? with
      | some σ => result.aborted = false ∧ verify pk msg σ = true
      | none => result.aborted = true

theorem sign_result_accepts (spec : Spec p) (seed msg : ByteArray) :
    let result := spec.sign (spec.keygen seed).2 msg
    result.accepts := by
  dsimp [SigningResult.accepts]
  have h :=
    spec.verify_sign seed msg (spec.keygen seed).1 (spec.keygen seed).2
      (spec.sign (spec.keygen seed).2 msg) rfl rfl
  cases hsig : (spec.sign (spec.keygen seed).2 msg).signature? with
  | none =>
      simpa [hsig] using h
  | some σ =>
      have h' :
          (spec.sign (spec.keygen seed).2 msg).aborted = false ∧
            spec.verify (spec.keygen seed).1 msg σ = true := by
        simpa [hsig] using h
      simpa [SigningResult.accepts, hsig] using h'.1

theorem sign_result_matches_verify (spec : Spec p) (seed msg : ByteArray) :
    match (spec.sign (spec.keygen seed).2 msg).signature? with
    | some σ =>
        (spec.sign (spec.keygen seed).2 msg).aborted = false ∧
          spec.verify (spec.keygen seed).1 msg σ = true
    | none =>
        (spec.sign (spec.keygen seed).2 msg).aborted = true := by
  simpa using
    spec.verify_sign seed msg (spec.keygen seed).1 (spec.keygen seed).2
      (spec.sign (spec.keygen seed).2 msg) rfl rfl

theorem sign_result_signature_hint_bound (spec : Spec p) (seed msg : ByteArray)
    {σ : Signature p} :
    (spec.sign (spec.keygen seed).2 msg).signature? = some σ →
      (spec.sigRepr σ).hintWeight ≤ p.ω := by
  intro hσ
  have hverify :
      (spec.sign (spec.keygen seed).2 msg).aborted = false ∧
        spec.verify (spec.keygen seed).1 msg σ = true := by
    simpa [hσ] using sign_result_matches_verify (p := p) spec seed msg
  exact spec.verify_hint_bound (spec.keygen seed).1 msg σ hverify.2

end FIPS204
end DSA
end Crypto
end HeytingLean
