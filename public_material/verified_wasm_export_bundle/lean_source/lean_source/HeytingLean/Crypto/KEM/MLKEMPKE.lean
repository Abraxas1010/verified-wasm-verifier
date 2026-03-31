import HeytingLean.Crypto.KEM.MLKEM203Params
import HeytingLean.Crypto.KEM.FujisakiOkamoto
import HeytingLean.Crypto.Lattice.FaithfulReductions
import HeytingLean.Crypto.Lattice.RecoveryViews
import Mathlib.Data.Matrix.Mul

/-!
# ML-KEM K-PKE (Base Encryption Scheme): spec-level algebra + correctness lemma

This file provides a **spec-first** K-PKE layer for ML-KEM-style constructions:

- We model keys/ciphertexts algebraically over the standard Kyber ring
  `Rq = (ZMod q)[X] ⧸ ⟨X^n + 1⟩` with module rank `k`.
- We do **not** implement sampling, compression, or serialization here.
- We prove a deterministic correctness theorem:
  `decrypt (encryptDet m r e1 e2) = m`,
  assuming a codec correctness condition `decode (encode m + noise) = m` under a `good noise`
  predicate.

This is the “Phase 4” base layer needed to connect (later) to:
1) concrete ML-KEM encoding/compression and
2) failure-probability analysis (δ).
-/

namespace HeytingLean
namespace Crypto
namespace KEM
namespace FIPS203

open scoped BigOperators

namespace KPKE

open HeytingLean.Crypto.Lattice

noncomputable section

/-- MLWE parameters induced from a FIPS 203 bundle. -/
abbrev P (p : MLKEM203Params) : Lattice.MLWEParams :=
  toMLWEParams p

abbrev Rq (p : MLKEM203Params) : Type :=
  Lattice.RingMLWE.Rq (P p)

abbrev ModVec (p : MLKEM203Params) : Type :=
  Lattice.RingMLWE.ModVec (P p)

abbrev ModMat (p : MLKEM203Params) : Type :=
  Lattice.RingMLWE.ModMat (P p)

/-- Message encoding/decoding interface, with a “good noise” predicate for correctness. -/
structure MsgCodec (p : MLKEM203Params) where
  Msg : Type
  encode : Msg → Rq p
  decode : Rq p → Msg
  good : Rq p → Prop
  correct : ∀ m e, good e → decode (encode m + e) = m

/-- Public key for K-PKE: matrix `A` and vector `t = A*s + e`. -/
structure PublicKey (p : MLKEM203Params) where
  A : ModMat p
  t : ModVec p

/-- Secret key for K-PKE: the secret vector `s`. -/
structure SecretKey (p : MLKEM203Params) where
  s : ModVec p

/-- Ciphertext for K-PKE: `u` (vector) and `v` (ring element). -/
structure Ciphertext (p : MLKEM203Params) where
  u : ModVec p
  v : Rq p

open Matrix

/-- Dot product for module vectors in the ring. -/
def dot {p : MLKEM203Params} (x y : ModVec p) : Rq p :=
  x ⬝ᵥ y

/-- Deterministic K-PKE encryption given explicit “randomness”/noise terms. -/
def encryptDet {p : MLKEM203Params} (codec : MsgCodec p) (pk : PublicKey p)
    (m : codec.Msg) (r e1 : ModVec p) (e2 : Rq p) : Ciphertext p :=
  { u := pk.Aᵀ.mulVec r + e1
  , v := dot pk.t r + e2 + codec.encode m
  }

/-- Deterministic K-PKE decryption given a message codec. -/
def decrypt {p : MLKEM203Params} (codec : MsgCodec p) (sk : SecretKey p) (ct : Ciphertext p) :
    codec.Msg :=
  codec.decode (ct.v - dot sk.s ct.u)

/-!
## Correctness (up to the codec’s “good noise” predicate)

If `t = A*s + e` and the induced residual noise satisfies `codec.good`, then decrypting an
encryption recovers the message.
-/

theorem dot_mulVec_eq_dot_mulVec_transpose {p : MLKEM203Params} (A : ModMat p) (s r : ModVec p) :
    dot (A.mulVec s) r = dot s (Aᵀ.mulVec r) := by
  classical
  -- Use standard matrix lemmas: `dotProduct_mulVec` and `mulVec_transpose`.
  -- First, commute to match the lemma orientation.
  have h₁ : dot (A.mulVec s) r = dot r (A.mulVec s) := by
    simpa [dot] using (dotProduct_comm (A.mulVec s) r)
  -- Associate to the left.
  have h₂ : dot r (A.mulVec s) = dot (r ᵥ* A) s := by
    simpa [dot] using (dotProduct_mulVec (v := r) (A := A) (w := s))
  -- Commute and rewrite `r ᵥ* A` as `Aᵀ.mulVec r`.
  have h₃ : dot (r ᵥ* A) s = dot s (Aᵀ.mulVec r) := by
    have : r ᵥ* A = Aᵀ.mulVec r := (mulVec_transpose (A := A) (x := r)).symm
    calc
      dot (r ᵥ* A) s = dot s (r ᵥ* A) := by
        simpa [dot] using (dotProduct_comm (r ᵥ* A) s)
      _ = dot s (Aᵀ.mulVec r) := by simp [dot, this]
  exact h₁.trans (h₂.trans h₃)

theorem decrypt_encryptDet {p : MLKEM203Params} (codec : MsgCodec p) (pk : PublicKey p)
    (sk : SecretKey p) (e : ModVec p)
    (ht : pk.t = pk.A.mulVec sk.s + e)
    (m : codec.Msg) (r e1 : ModVec p) (e2 : Rq p)
    (hgood : codec.good (dot e r + e2 - dot sk.s e1)) :
    decrypt codec sk (encryptDet codec pk m r e1 e2) = m := by
  classical
  -- Expand the definitions and reduce to the codec-correctness condition.
  have hdot_cancel :
      dot (pk.A.mulVec sk.s) r = dot sk.s (pk.Aᵀ.mulVec r) :=
    dot_mulVec_eq_dot_mulVec_transpose (A := pk.A) (s := sk.s) (r := r)
  have hdot_cancel' : (pk.A.mulVec sk.s) ⬝ᵥ r = sk.s ⬝ᵥ (pk.Aᵀ.mulVec r) := by
    change dot (pk.A.mulVec sk.s) r = dot sk.s (pk.Aᵀ.mulVec r)
    exact hdot_cancel
  -- Compute `ct.v - s⋅ct.u` and simplify.
  have hres :
      (encryptDet codec pk m r e1 e2).v - dot sk.s (encryptDet codec pk m r e1 e2).u
        = codec.encode m + (dot e r + e2 - dot sk.s e1) := by
    -- Expand `u`/`v` and use bilinearity of dot-product plus additive commutativity.
    simp [encryptDet, dot, ht, hdot_cancel', sub_eq_add_neg]
    abel_nf
  -- Apply the codec correctness theorem.
  simp [decrypt, hres, codec.correct _ _ hgood]

theorem encryptDet_residual {p : MLKEM203Params} (codec : MsgCodec p) (pk : PublicKey p)
    (sk : SecretKey p) (e : ModVec p)
    (ht : pk.t = pk.A.mulVec sk.s + e)
    (m : codec.Msg) (r e1 : ModVec p) (e2 : Rq p) :
    (encryptDet codec pk m r e1 e2).v - dot sk.s (encryptDet codec pk m r e1 e2).u
      = codec.encode m + (dot e r + e2 - dot sk.s e1) := by
  classical
  have hdot_cancel :
      dot (pk.A.mulVec sk.s) r = dot sk.s (pk.Aᵀ.mulVec r) :=
    dot_mulVec_eq_dot_mulVec_transpose (A := pk.A) (s := sk.s) (r := r)
  have hdot_cancel' : (pk.A.mulVec sk.s) ⬝ᵥ r = sk.s ⬝ᵥ (pk.Aᵀ.mulVec r) := by
    change dot (pk.A.mulVec sk.s) r = dot sk.s (pk.Aᵀ.mulVec r)
    exact hdot_cancel
  simp [encryptDet, dot, ht, hdot_cancel', sub_eq_add_neg]
  abel_nf

/-!
## Security statements

The game-based IND-CPA security of K-PKE and its reduction to MLWE is tracked as higher-level
work; here we only provide stable names in the namespace.
-/

open HeytingLean.Crypto.KEM.FujisakiOkamoto

/-- Imported statement bundle for the base K-PKE IND-CPA surface. -/
structure INDCPAStatementBundle (p : MLKEM203Params) where
  parameterSet : String
  mlweParams : Lattice.MLWEParams
  proofSource : ExternalReference
  correctnessTheorem : String
  implementationBoundary : String
  claimSummary : String
  deriving Repr

/-- Repository-native IND-CPA statement surface for the ML-KEM base encryption scheme. -/
abbrev IND_CPA (p : MLKEM203Params) : Type := INDCPAStatementBundle p

def importedINDCPA (p : MLKEM203Params) : IND_CPA p :=
  { parameterSet := p.name
    mlweParams := toMLWEParams p
    proofSource := kyberEpisodeV2024
    correctnessTheorem := "decrypt_encryptDet"
    implementationBoundary := "Distribution-level IND-CPA proof remains imported from the external proof line."
    claimSummary :=
      "The base K-PKE layer exposes algebraic correctness natively and tracks IND-CPA as an imported MLWE-backed statement surface." }

/-- Statement shape for deriving K-PKE IND-CPA from MLWE hardness. -/
structure IND_CPA_under_MLWE (p : MLKEM203Params) where
  derive : Lattice.Unsolvable (Lattice.MLWEView (toMLWEParams p)) → IND_CPA p

theorem importedINDCPA_parameterSet (p : MLKEM203Params) :
    (importedINDCPA p).parameterSet = p.name := rfl

theorem importedINDCPA_correctnessTheorem (p : MLKEM203Params) :
    (importedINDCPA p).correctnessTheorem = "decrypt_encryptDet" := rfl

theorem importedINDCPA_residual_matches_local_theorem (p : MLKEM203Params)
    (codec : MsgCodec p) (pk : PublicKey p) (sk : SecretKey p) (e : ModVec p)
    (ht : pk.t = pk.A.mulVec sk.s + e)
    (m : codec.Msg) (r e1 : ModVec p) (e2 : Rq p) :
    (importedINDCPA p).mlweParams = toMLWEParams p ∧
      (encryptDet codec pk m r e1 e2).v - dot sk.s (encryptDet codec pk m r e1 e2).u
        = codec.encode m + (dot e r + e2 - dot sk.s e1) := by
  exact ⟨rfl, encryptDet_residual codec pk sk e ht m r e1 e2⟩

theorem importedINDCPA_uses_local_correctness (p : MLKEM203Params)
    (codec : MsgCodec p) (pk : PublicKey p) (sk : SecretKey p) (e : ModVec p)
    (ht : pk.t = pk.A.mulVec sk.s + e)
    (m : codec.Msg) (r e1 : ModVec p) (e2 : Rq p)
    (hgood : codec.good (dot e r + e2 - dot sk.s e1)) :
    (importedINDCPA p).correctnessTheorem = "decrypt_encryptDet" ∧
      decrypt codec sk (encryptDet codec pk m r e1 e2) = m := by
  exact ⟨rfl, decrypt_encryptDet codec pk sk e ht m r e1 e2 hgood⟩

end

end KPKE

end FIPS203
end KEM
end Crypto
end HeytingLean
