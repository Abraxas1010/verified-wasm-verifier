import Lean
import HeytingLean.Analysis.Graph.Spectral

open HeytingLean.Analysis.Graph

private def parseArg (xs : List String) (flag : String) : Option String :=
  match xs with
  | [] => none
  | x::y::rest => if x = flag then some y else parseArg (y::rest) flag
  | _ => none

private def parseEdges (s : String) : Array (Nat × Nat) :=
  let items := s.splitOn ","
  items.foldl (init := #[]) (fun acc e =>
    match e.splitOn "-" with
    | [a,b] =>
      match (a.trim).toNat?, (b.trim).toNat? with
      | some u, some v => acc.push (u,v)
      | _, _ => acc
    | _ => acc)

private def parseListFloat (s : String) : Array Float :=
  s.splitOn "," |>.foldl (init := #[]) (fun acc t => match t.toInt? with | some v => acc.push (Float.ofInt v) | none => acc)

def main (argv : List String) : IO Unit := do
  let some n := (parseArg argv "--n").bind (·.toNat?)
    | IO.eprintln "usage: graph_ft --n N --edges u-v,u-v [--x v1,...] [--k K]"; IO.Process.exit 1
  let esStr := (parseArg argv "--edges").getD ""
  let es := parseEdges esStr
  let k := (parseArg argv "--k").bind (·.toNat?) |>.getD 3
  let xs := (parseArg argv "--x").map parseListFloat |>.getD (Array.replicate n 1.0)
  if xs.size ≠ n then IO.eprintln "len(x) != n"; IO.Process.exit 1
  let g : Edges := { n := n, pairs := es }
  let vecs := kEigen g k 30
  let coeffs := project vecs xs
  let vs := vecs.map (fun v => "[" ++ String.intercalate "," (v.map (fun z => toString z)).toList ++ "]")
  let cs := String.intercalate "," (coeffs.map (fun c => toString c)).toList
  let json := "{" ++ s!"\"n\":{n}," ++ s!"\"k\":{min k n}," ++
    "\"eigen\":[" ++ String.intercalate "," vs.toList ++ "]," ++
    "\"coeffs\":[" ++ cs ++ "]}"
  IO.println json

