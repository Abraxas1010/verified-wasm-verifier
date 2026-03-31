import HeytingLean.CCI.Version

namespace HeytingLean.Tests.TCBMetadata

open HeytingLean.CCI

def expect (msg : String) (b : Bool) : IO Unit := do
  if b then
    pure ()
  else
    throw <| IO.userError s!"TCBMetadata test failed: {msg}"

def isNonemptyDigits (s : String) : Bool :=
  s.length > 0 && s.all Char.isDigit

def run : IO Unit := do
  expect "IRv not digits" (isNonemptyDigits IRv)
  expect "RewriteTablev not digits" (isNonemptyDigits RewriteTablev)
  expect "Canonv not digits" (isNonemptyDigits Canonv)
  expect "Circuitv not digits" (isNonemptyDigits Circuitv)

def main (_args : List String) : IO UInt32 := do
  try
    run
    IO.println "TCB metadata passed"
    pure 0
  catch e =>
    IO.eprintln e
    pure 1

end HeytingLean.Tests.TCBMetadata

/-- expose test entry point for lake target. -/
def main (args : List String) : IO UInt32 :=
  HeytingLean.Tests.TCBMetadata.main args

