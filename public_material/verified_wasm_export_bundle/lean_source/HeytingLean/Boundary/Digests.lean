import Lean
import Lean.Data.Json
import HeytingLean.Crypto.Commit

namespace HeytingLean
namespace Boundary
namespace Digests

open Lean

/-- Canonicalization digest: domain‑separated commit over a canonical JSON string. -/
def canonDigest (policyCanonicalJson : String) : String :=
  HeytingLean.Crypto.commitString "APMT:CANON" policyCanonicalJson

structure StmtInputs where
  parentReceiptHash : String
  toAddr            : Nat
  vendor            : Nat
  amount            : Nat
  now               : Nat
  deriving Repr

def stmtInputsToJson (s : StmtInputs) : Json :=
  Json.mkObj [
    ("parent", Json.str s.parentReceiptHash),
    ("toAddr", Json.str (toString s.toAddr)),
    ("vendor", Json.str (toString s.vendor)),
    ("amount", Json.str (toString s.amount)),
    ("now", Json.str (toString s.now))
  ]

/-- Statement hash: domain‑separated commit over canonicalized inputs. -/
def stmtHash (s : StmtInputs) : String :=
  HeytingLean.Crypto.commitString "APMT:STMT" (stmtInputsToJson s |>.compress)

end Digests
end Boundary
end HeytingLean
