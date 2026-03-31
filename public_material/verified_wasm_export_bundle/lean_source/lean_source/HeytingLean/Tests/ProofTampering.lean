import HeytingLean.CCI.Check
import HeytingLean.CCI.Cert

namespace HeytingLean.Tests.ProofTampering

open HeytingLean.CCI

def expect (msg : String) (b : Bool) : IO Unit := do
  if b then
    pure ()
  else
    throw <| IO.userError s!"ProofTampering test failed: {msg}"

def mkTamperedCert : Certificate :=
  let omega := Expr.impR (Expr.atom "P") (Expr.atom "Q")
  let wrong : Digest := ByteArray.mk #[0x00, 0x01]
  { inputs := []
  , omega := omega
  , lensImgs := []
  , rewrites := []
  , digests := [("omega", wrong)] }

def run : IO Unit := do
  expect "check accepted a tampered certificate" (!check mkTamperedCert)

def main (_args : List String) : IO UInt32 := do
  try
    run
    IO.println "Proof tampering detection passed"
    pure 0
  catch e =>
    IO.eprintln e
    pure 1

end HeytingLean.Tests.ProofTampering

/-- expose test entry point for lake target. -/
def main (args : List String) : IO UInt32 :=
  HeytingLean.Tests.ProofTampering.main args

