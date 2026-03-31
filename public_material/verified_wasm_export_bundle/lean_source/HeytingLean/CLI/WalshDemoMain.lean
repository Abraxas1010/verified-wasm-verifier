import Lean
import HeytingLean.Analysis.Walsh

open HeytingLean.Analysis

private def parseArg (xs : List String) (flag : String) : Option String :=
  match xs with
  | [] => none
  | x::y::rest => if x = flag then some y else parseArg (y::rest) flag
  | _ => none

private def parseListInt (s : String) : Array Int :=
  let parts := s.splitOn ","
  parts.foldl (init := #[]) (fun acc t =>
    match t.toInt? with
    | some v => acc.push v
    | none   => acc)

def main (argv : List String) : IO Unit := do
  let vals := (parseArg argv "--vals").map parseListInt |>.getD (#[1, 1, -1, -1])
  let w := walsh vals
  let arrStr := String.intercalate "," ((w.map (fun z => toString z)).toList)
  let json := "{" ++ "\"input\":[" ++ String.intercalate "," ((vals.map (fun z => toString z)).toList) ++ "],"
    ++ "\"walsh\":[" ++ arrStr ++ "]}"
  IO.println json
