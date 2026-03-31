import Lean
import HeytingLean.Util.SHA

/-!
Commitment interface for schema commitments and lens outputs.

Default implementation: domain-separated SHA-256 (hex).
Future: replace with Poseidon/Rescue gadgets in the circuit-backed implementation.
-/

namespace HeytingLean
namespace Crypto

def commitString (domain : String) (s : String) : String :=
  let payload := (domain ++ ":" ++ s).toUTF8
  let hex := HeytingLean.Util.SHA256.sha256Hex payload
  s!"sha256:{domain}:{hex}"

end Crypto
end HeytingLean
