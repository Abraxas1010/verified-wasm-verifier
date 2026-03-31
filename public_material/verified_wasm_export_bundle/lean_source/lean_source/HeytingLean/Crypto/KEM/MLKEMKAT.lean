import HeytingLean.Crypto.KEM.MLKEM203Params
import HeytingLean.Crypto.KAT.RSP
import Lean

/-!
# ML-KEM KAT (Known Answer Test) utilities (parsing + structural validation)

This module does **not** implement real ML-KEM in Lean. Instead, it provides:

- a thin IO layer to parse NIST `.rsp` vectors via the existing `Crypto.KAT.RSP` parser;
- structural checks that hex payload sizes match the FIPS 203 parameter bundle.

For full byte-level parity, use the existing runner infrastructure:
- `lake exe kem_kat_runner` (counting and parity orchestration)
- `lake exe kem_parity` and external CLIs (when available)

Reference: https://github.com/post-quantum-cryptography/KAT (vector corpus).
-/

namespace HeytingLean
namespace Crypto
namespace KEM
namespace FIPS203
namespace KAT

open System

private def hexBytes (s : String) : Nat :=
  Nat.div (HeytingLean.Crypto.KAT.normHex s |>.length) 2

private def checkCaseSizes (p : MLKEM203Params) (c : HeytingLean.Crypto.KAT.KEMRSPCase) : Bool :=
  -- Treat `pkHex/skHex/ctHex/ssHex` as raw hex payloads; compare byte lengths.
  let pkOk := hexBytes c.pkHex == p.ekSize
  let skOk := hexBytes c.skHex == p.dkSize
  let ctOk := hexBytes c.ctHex == p.ctSize
  -- Shared secret is 32 bytes in ML-KEM.
  let ssOk := hexBytes c.ssHex == 32
  pkOk && skOk && ctOk && ssOk

def checkRSPFile (p : MLKEM203Params) (path : FilePath) : IO Bool := do
  let cases ← HeytingLean.Crypto.KAT.parseKEMRSPFile path
  if cases.isEmpty then
    return false
  return cases.all (checkCaseSizes p)

end KAT
end FIPS203
end KEM
end Crypto
end HeytingLean
