import Lean.Data.Json
import HeytingLean.CCI.Core
import HeytingLean.CCI.Json
import HeytingLean.CCI.RewriteTable
import HeytingLean.CCI.Version
import HeytingLean.Util.SHA

/-!
# Certificates (v1)

Minimal certificate envelope for exporter/checker.
-/

namespace HeytingLean
namespace CCI
open Lean

abbrev PublicInputs := List (String × String)
abbrev LensVal := Lens
abbrev Path := String

structure Certificate where
  inputs   : PublicInputs
  omega    : Expr
  lensImgs : List LensVal
  rewrites : List RuleId
  digests  : List (Path × Digest)
  -- no deriving needed in production; keep lean

def encodeDigest (d : Digest) : Json :=
  -- encode as hex string for portability
  let parts : List String := d.toList.map (fun b =>
    let s := (Nat.toDigits 16 b.toNat).asString
    if s.length = 1 then "0" ++ s else s)
  let hex := String.intercalate "" parts
  Json.str hex

def digestOfString (s : String) : Digest :=
  HeytingLean.Util.SHA256.sha256Bytes s.toUTF8

def hashExpr : Expr → Digest :=
  fun e =>
    -- domain‑separated, versioned hash payload
    let payload := "LoFΩ|" ++ HeytingLean.CCI.IRv ++ "|" ++ e.structuralKey
    digestOfString payload


end CCI
end HeytingLean
