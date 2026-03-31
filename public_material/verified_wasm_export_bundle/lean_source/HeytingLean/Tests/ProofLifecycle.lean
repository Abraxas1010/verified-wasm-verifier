import HeytingLean.CCI.Check
import HeytingLean.CCI.Cert

namespace HeytingLean.Tests.ProofLifecycle

open HeytingLean.CCI

def expect (msg : String) (b : Bool) : IO Unit := do
  if b then
    pure ()
  else
    throw <| IO.userError s!"ProofLifecycle test failed: {msg}"

def mkGoodCert : Certificate :=
  let omega := Expr.impR (Expr.atom "P") (Expr.atom "Q")
  let d := hashExpr (canon omega)
  { inputs := []
  , omega := omega
  , lensImgs := []
  , rewrites := []
  , digests := [("omega", d)] }

def run : IO Unit := do
  expect "check rejected a correct certificate" (check mkGoodCert)

def main (_args : List String) : IO UInt32 := do
  try
    run
    IO.println "Proof lifecycle passed"
    pure 0
  catch e =>
    IO.eprintln e
    pure 1

end HeytingLean.Tests.ProofLifecycle

/-- expose test entry point for lake target. -/
def main (args : List String) : IO UInt32 :=
  HeytingLean.Tests.ProofLifecycle.main args

