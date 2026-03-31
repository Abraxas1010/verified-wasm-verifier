import HeytingLean.Crypto.KEM.MLKEMPKE
import HeytingLean.Crypto.KEM.MLKEMCompress
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Abel

/-!
# ML-KEM K-PKE with compression (spec-level wiring)

This file layers FIPS 203 compression on top of the K-PKE spec layer from `MLKEMPKE.lean`.

We:
- define a compressed ciphertext carrier (coefficient-wise compression for `u` and `v`);
- define `encryptCompressed` / `decryptCompressed` by (de)compressing around `encryptDet` / `decrypt`;
- prove a **codec-conditional** correctness theorem by threading an explicit compression-noise term.

We do **not** prove tight numerical compression error bounds here; those bounds can be supplied
separately and then used to discharge the `codec.good` predicate.
-/

namespace HeytingLean
namespace Crypto
namespace KEM
namespace FIPS203

open scoped BigOperators
open HeytingLean.Crypto.Lattice
open Matrix

namespace KPKECompressed

open HeytingLean.Crypto.KEM.FIPS203.KPKE
open HeytingLean.Crypto.KEM.FIPS203.Compress

noncomputable section

abbrev P (p : MLKEM203Params) : Lattice.MLWEParams := toMLWEParams p
abbrev Rq (p : MLKEM203Params) : Type := KPKE.Rq p
abbrev ModVec (p : MLKEM203Params) : Type := KPKE.ModVec p

/-- Coefficient-wise compressed ciphertext for K-PKE. -/
structure CompressedCiphertext (p : MLKEM203Params) where
  u : Fin (P p).k → CompressedPoly (P p).n p.du
  v : CompressedPoly (P p).n p.dv

noncomputable def compressCt {p : MLKEM203Params} (ct : KPKE.Ciphertext p) : CompressedCiphertext p :=
  { u := compressModVec (P := P p) p.du (x := (show RingReductions.RModVec (P p) from ct.u))
  , v := compressRq (P := P p) p.dv (x := (show RingReductions.Rq (P p) from ct.v))
  }

noncomputable def decompressCt {p : MLKEM203Params} (ct : CompressedCiphertext p) : KPKE.Ciphertext p :=
  { u := (show KPKE.ModVec p from decompressModVec (P := P p) p.du ct.u)
  , v := (show KPKE.Rq p from decompressRq (P := P p) p.dv ct.v)
  }

/-- K-PKE encryption with compression (deterministic, given explicit noise terms). -/
noncomputable def encryptCompressed {p : MLKEM203Params} (codec : KPKE.MsgCodec p) (pk : KPKE.PublicKey p)
    (m : codec.Msg) (r e1 : ModVec p) (e2 : Rq p) : CompressedCiphertext p :=
  compressCt (p := p) (KPKE.encryptDet codec pk m r e1 e2)

/-- K-PKE decryption after decompression. -/
noncomputable def decryptCompressed {p : MLKEM203Params} (codec : KPKE.MsgCodec p) (sk : KPKE.SecretKey p)
    (ct : CompressedCiphertext p) : codec.Msg :=
  KPKE.decrypt codec sk (decompressCt (p := p) ct)

/-- Generic correctness helper: if the decryption argument equals `encode m + noise`, decode returns `m`. -/
theorem decrypt_of_eq_encode_add {p : MLKEM203Params} (codec : KPKE.MsgCodec p) (sk : KPKE.SecretKey p)
    (ct : KPKE.Ciphertext p) (m : codec.Msg) (noise : Rq p)
    (h : ct.v - KPKE.dot sk.s ct.u = codec.encode m + noise) (hgood : codec.good noise) :
    KPKE.decrypt codec sk ct = m := by
  simp [KPKE.decrypt, h, codec.correct _ _ hgood]

/-- Compression noise injected into the decryption expression. -/
noncomputable def compressionNoise {p : MLKEM203Params} (sk : KPKE.SecretKey p) (ct : KPKE.Ciphertext p) : Rq p :=
  ((show KPKE.Rq p from
      decompressRq (P := P p) p.dv (compressRq (P := P p) p.dv (show RingReductions.Rq (P p) from ct.v)))
      - ct.v)
    -
    KPKE.dot sk.s
      ((show KPKE.ModVec p from
          decompressModVec (P := P p) p.du
            (compressModVec (P := P p) p.du (show RingReductions.RModVec (P p) from ct.u)))
        - ct.u)

/-- Correctness with compression: decryption succeeds if residual+compressionNoise is “good”. -/
theorem decrypt_encryptCompressed {p : MLKEM203Params} (codec : KPKE.MsgCodec p) (pk : KPKE.PublicKey p)
    (sk : KPKE.SecretKey p) (e : ModVec p)
    (ht : pk.t = pk.A.mulVec sk.s + e)
    (m : codec.Msg) (r e1 : ModVec p) (e2 : Rq p)
    (hgood :
      codec.good (KPKE.dot e r + e2 - KPKE.dot sk.s e1 + compressionNoise (p := p) sk (KPKE.encryptDet codec pk m r e1 e2))) :
    decryptCompressed (p := p) codec sk (encryptCompressed (p := p) codec pk m r e1 e2) = m := by
  classical
  -- Reduce to the plain decryption expression, then apply the generic helper with the computed noise.
  have hplain :
      (decompressCt (p := p) (encryptCompressed (p := p) codec pk m r e1 e2)).v
        - KPKE.dot sk.s (decompressCt (p := p) (encryptCompressed (p := p) codec pk m r e1 e2)).u
        =
        (KPKE.encryptDet codec pk m r e1 e2).v - KPKE.dot sk.s (KPKE.encryptDet codec pk m r e1 e2).u
          + compressionNoise (p := p) sk (KPKE.encryptDet codec pk m r e1 e2) := by
    -- `decompressCt (compressCt ct)` expands into the decompression of compressed `u`/`v`.
    -- Collect the difference from the original ciphertext as `compressionNoise`.
    simp [encryptCompressed, compressCt, decompressCt, compressionNoise, sub_eq_add_neg, KPKE.dot]
    abel_nf

  -- Use the residual-noise computation from the Phase 4 correctness theorem.
  have hres :
      (KPKE.encryptDet codec pk m r e1 e2).v - KPKE.dot sk.s (KPKE.encryptDet codec pk m r e1 e2).u
        = codec.encode m + (KPKE.dot e r + e2 - KPKE.dot sk.s e1) :=
    KPKE.encryptDet_residual (codec := codec) (pk := pk) (sk := sk) (e := e) (ht := ht)
      (m := m) (r := r) (e1 := e1) (e2 := e2)

  have hdecode :
      KPKE.decrypt codec sk (decompressCt (p := p) (encryptCompressed (p := p) codec pk m r e1 e2)) = m := by
    -- Assemble the decryption argument as `encode m + (residual + compressionNoise)`.
    refine decrypt_of_eq_encode_add (codec := codec) (sk := sk)
      (ct := decompressCt (p := p) (encryptCompressed (p := p) codec pk m r e1 e2))
      (m := m)
      (noise := (KPKE.dot e r + e2 - KPKE.dot sk.s e1) + compressionNoise (p := p) sk (KPKE.encryptDet codec pk m r e1 e2))
      ?_ ?_
    · calc
        (decompressCt (p := p) (encryptCompressed (p := p) codec pk m r e1 e2)).v
            - KPKE.dot sk.s (decompressCt (p := p) (encryptCompressed (p := p) codec pk m r e1 e2)).u
            =
          (KPKE.encryptDet codec pk m r e1 e2).v - KPKE.dot sk.s (KPKE.encryptDet codec pk m r e1 e2).u
            + compressionNoise (p := p) sk (KPKE.encryptDet codec pk m r e1 e2) := hplain
        _ = codec.encode m + ((KPKE.dot e r + e2 - KPKE.dot sk.s e1) + compressionNoise (p := p) sk (KPKE.encryptDet codec pk m r e1 e2)) := by
          simp [hres, add_assoc, add_left_comm, add_comm]
    · -- `hgood` is stated with exactly this noise term (up to associativity/commutativity).
      simpa [compressionNoise, add_assoc, add_left_comm, add_comm] using hgood

  simpa [decryptCompressed] using hdecode

end

end KPKECompressed

end FIPS203
end KEM
end Crypto
end HeytingLean
