import Lean
import HeytingLean.Analysis.DFTFloat

open HeytingLean.Analysis.DFTFloat

private def parseArg (xs : List String) (flag : String) : Option String :=
  match xs with
  | [] => none
  | x::y::rest => if x = flag then some y else parseArg (y::rest) flag
  | _ => none

private def parseList (s : String) : Array Float :=
  s.splitOn "," |>.foldl (init := #[]) (fun acc t => match t.toInt? with | some v => acc.push (Float.ofInt v) | none => acc)

def main (argv : List String) : IO Unit := do
  let xs := (parseArg argv "--x").map parseList |>.getD (#[1,0,-1,0])
  if xs.isEmpty then IO.eprintln "empty input"; IO.Process.exit 1
  let X := dft xs
  let xr := idft X
  let spec := String.intercalate "," ((X.map (fun p => s!"[{p.fst},{p.snd}] ")).toList)
  let recon := String.intercalate "," ((xr.map (fun r => s!"{r}")).toList)
  let json := "{" ++ "\"spectrum\":[" ++ spec ++ "]," ++ "\"recon\":[" ++ recon ++ "]}"
  IO.println json
