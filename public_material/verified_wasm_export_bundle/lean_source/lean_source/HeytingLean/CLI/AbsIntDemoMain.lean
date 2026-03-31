import Lean
import HeytingLean.Bridges.AbsInt

open HeytingLean.Bridges

private def parseArg (xs : List String) (flag : String) : Option String :=
  match xs with
  | [] => none
  | x::y::rest => if x = flag then some y else parseArg (y::rest) flag
  | _ => none

def main (argv : List String) : IO Unit := do
  let lo := (parseArg argv "--lo").bind (·.toInt?) |>.getD 0
  let hi := (parseArg argv "--hi").bind (·.toInt?) |>.getD lo
  let a : AbsInt.Interval := { lo := lo, hi := hi }
  let ai := AbsInt.I a
  let s := "{" ++
    "\"lo\":" ++ toString a.lo ++ "," ++
    "\"hi\":" ++ toString a.hi ++ "," ++
    "\"I\":{" ++ "\"lo\":" ++ toString ai.lo ++ "," ++ "\"hi\":" ++ toString ai.hi ++ "}}"
  IO.println s
