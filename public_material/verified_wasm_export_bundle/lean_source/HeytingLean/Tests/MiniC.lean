import HeytingLean.MiniC.Syntax
import HeytingLean.MiniC.Semantics

open HeytingLean
open HeytingLean.MiniC

namespace HeytingLean.Tests.MiniC

/-- MiniC function `return x + 1;`. -/
def add1Fun : Fun :=
  { name := "add1"
    params := ["x"]
    body :=
      Stmt.return <|
        Expr.add (Expr.var "x") (Expr.intLit 1) }

/-- Program whose main is `add1`. -/
def add1Program : Program :=
  { defs := [add1Fun]
    main := add1Fun }

/-- Expect equality helper for MiniC values. -/
def expectEq (msg : String) (a b : Val) : IO Unit :=
  if decide (a = b) then
    pure ()
  else
    throw <| IO.userError s!"MiniC test failed: {msg}"

/-- Run `add1` on a single integer input. -/
def runCase (n : Int) : IO Unit := do
  match runProgram add1Program [Val.int n] with
  | some v => expectEq (s!"add1 {n}") v (Val.int (n + 1))
  | none => throw <| IO.userError s!"MiniC execution failed on input {n}"

/-- Execute a few sample inputs. -/
def run : IO Unit := do
  for n in [0, 1, 41, 128] do
    runCase n

/-- Entry point for `lake exe test_minic_basics`. -/
def main (_args : List String) : IO UInt32 := do
  try
    run
    IO.println "MiniC basics passed"
    pure 0
  catch e =>
    IO.eprintln e
    pure 1

end HeytingLean.Tests.MiniC

/-- expose CLI entry point --/
def main (args : List String) : IO UInt32 :=
  HeytingLean.Tests.MiniC.main args
