import HeytingLean.CCI.Check
import HeytingLean.CCI.Cert

namespace HeytingLean.Tests.SecurityValidation

open HeytingLean.CCI

def expect (msg : String) (b : Bool) : IO Unit := do
  if b then
    pure ()
  else
    throw <| IO.userError s!"SecurityValidation test failed: {msg}"

def run : IO Unit := do
  let omega := Expr.andR (Expr.atom "a") (Expr.andR (Expr.atom "b") (Expr.atom "a"))
  let canonOnce := canon omega
  let canonTwice := canon canonOnce
  expect "canon not idempotent on sample" (decide (canonOnce = canonTwice))

def main (_args : List String) : IO UInt32 := do
  try
    run
    IO.println "Security validation passed"
    pure 0
  catch e =>
    IO.eprintln e
    pure 1

end HeytingLean.Tests.SecurityValidation

/-- expose test entry point for lake target. -/
def main (args : List String) : IO UInt32 :=
  HeytingLean.Tests.SecurityValidation.main args

