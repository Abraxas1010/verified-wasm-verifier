import Lean
import HeytingLean.Crypto.ZK.R1CS

/-!
Types and helpers for a minimal on-chain style verifier surface.
This module is pure Lean and shared between chain/off-chain callers.
-/

namespace HeytingLean
namespace Chain

/- EVM 256-bit word (big-endian). -/
structure EVMWord where
  bytes : ByteArray

namespace EVMWord

private def padLeft (b : ByteArray) (n : Nat) : ByteArray :=
  if b.size ≥ n then b else Id.run do
    let mut out := ByteArray.emptyWithCapacity n
    let pad := n - b.size
    for _i in [:pad] do out := out.push 0
    let mut out2 := out
    for i in [:b.size] do
      out2 := out2.push (b.get! i)
    out2

def fromNat (n : Nat) : EVMWord :=
  let rec loop (x : Nat) (acc : List UInt8) : List UInt8 :=
    if x = 0 then acc else
      let byte : UInt8 := UInt8.ofNat (x % 256)
      loop (x / 256) (byte :: acc)
  let rawList := loop n []
  let raw := Id.run do
    let mut ba := ByteArray.empty
    for b in rawList do
      ba := ba.push b
    ba
  let be := padLeft raw 32
  { bytes := be }

-- toHex omitted for now (not required in current path)

end EVMWord

structure VerificationKey where
  -- Optional metadata for sanity; in a production SNARK this would be curve-specific.
  publicIndices : List Nat := []
  compiledSystemHash : String := ""
  deriving Repr, Inhabited

open Crypto.ZK

def checkSatisfaction (sys : System) (assign : Var → ℚ) : Bool :=
  sys.constraints.all (fun c => ((c.A.eval assign) * (c.B.eval assign)) == (c.C.eval assign))

end Chain
end HeytingLean
