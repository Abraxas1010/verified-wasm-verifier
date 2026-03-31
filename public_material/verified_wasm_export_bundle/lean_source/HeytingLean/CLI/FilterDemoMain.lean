import Lean
import HeytingLean.Analysis.Projectors

open HeytingLean.Analysis

private def parseArg (xs : List String) (flag : String) : Option String :=
  match xs with
  | [] => none
  | x::y::rest => if x = flag then some y else parseArg (y::rest) flag
  | _ => none

private def parseListFloat (s : String) : Array Float :=
  s.splitOn "," |>.foldl (init := #[]) (fun acc t => match t.toInt? with | some v => acc.push (Float.ofInt v) | none => acc)

def main (argv : List String) : IO Unit := do
  let xs := (parseArg argv "--x").map parseListFloat |>.getD (#[1,2,3,4,5,6])
  let window := (parseArg argv "--window").bind (·.toNat?) |>.getD (xs.size)
  let low := (parseArg argv "--lowpass").bind (·.toNat?) |>.getD 0
  let xw := timeWindow window xs
  -- crude "spectrum" pair up re/im as (x,0) and apply lowpass
  let specIn : Array (Float × Float) := xw.map (fun v => (v, 0.0))
  let specOut := if low = 0 then specIn else lowpass low specIn
  let xStr := String.intercalate "," (xs.map (fun v => toString v)).toList
  let wStr := String.intercalate "," (xw.map (fun v => toString v)).toList
  let sStr := String.intercalate "," (specOut.map (fun p => s!"[{p.fst},{p.snd}] ")).toList
  let json := "{" ++ s!"\"window\":{window}," ++ s!"\"lowpass\":{low}," ++
    "\"input\":[" ++ xStr ++ "]," ++ "\"windowed\":[" ++ wStr ++ "]," ++
    "\"spectrum\":[" ++ sStr ++ "]}"
  IO.println json

