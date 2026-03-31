import Lean
import HeytingLean.Analysis.Walsh

open HeytingLean.Analysis

structure Lit where
  var : Nat   -- 1-based
  neg : Bool := false
deriving Repr

abbrev Clause := Array Lit
abbrev CNF := Array Clause

private def parseNat (s : String) : Option Nat := s.toNat?

private def parseCNF (txt : String) : Option (Nat × CNF) := Id.run do
  let ls := txt.splitOn "\n" |>.map (·.trim) |>.filter (· ≠ "")
  if ls.isEmpty then return none
  let hdr := (ls[0]!).splitOn " " |>.filter (· ≠ "")
  if hdr.length < 2 then return none
  let some n := parseNat (hdr[0]!) | return none
  let some m := parseNat (hdr[1]!) | return none
  let mut clauses : CNF := #[]
  let body := ls.drop 1
  for i in [0:m] do
    if i < body.length then
      let line := body[i]!
      let lits := line.splitOn " " |>.filter (· ≠ "")
      let mut cs : Clause := #[]
      for tok in lits do
        if tok = "0" then () else
        let neg := tok.startsWith "-"
        let core := if neg then tok.drop 1 else tok
        let some vi := parseNat core | return none
        if vi = 0 ∨ vi > n then return none
        cs := cs.push { var := vi, neg }
      clauses := clauses.push cs
    else ()
  return some (n, clauses)

private def allAssignments (n : Nat) : Array (Array Bool) := Id.run do
  let m := Nat.pow 2 n
  let mut out : Array (Array Bool) := #[]
  for t in [0:m] do
    let mut a := Array.replicate n false
    for i in [0:n] do
      a := a.set! i (((t >>> i) &&& 1) = 1)
    out := out.push a
  return out

private def evalLit (a : Array Bool) (l : Lit) : Bool :=
  let idx := l.var - 1
  let v := a[idx]!
  if l.neg then !v else v

private def evalClause (a : Array Bool) (c : Clause) : Bool :=
  c.any (fun l => evalLit a l)

private def evalCNF (a : Array Bool) (f : CNF) : Bool :=
  f.all (fun c => evalClause a c)

private def parseArg (xs : List String) (flag : String) : Option String :=
  match xs with
  | [] => none
  | x::y::rest => if x = flag then some y else parseArg (y::rest) flag
  | _ => none

def main (argv : List String) : IO Unit := do
  let some path := parseArg argv "--file"
    | IO.eprintln "usage: sat_spectral --file <path>"; IO.Process.exit 1
  let contents ← IO.FS.readFile path
  let some (n, cnf) := parseCNF contents
    | IO.eprintln "parse error"; IO.Process.exit 1
  if n > 12 then
    IO.eprintln "n too large (<=12)"; IO.Process.exit 1
  let ass := allAssignments n
  let vals : Array Int := ass.map (fun a => if evalCNF a cnf then (1: Int) else 0)
  let w := walsh vals
  let energy : Int := w.foldl (init := 0) (fun acc v => acc + v*v)
  let topK := (w.map (fun z => Int.natAbs z)).qsort (· > ·) |>.extract 0 (min 5 w.size)
  let kStr := String.intercalate "," (topK.map (fun z => toString z)).toList
  let json := "{" ++
    s!"\"n\":{n}," ++
    s!"\"clauses\":{cnf.size}," ++
    s!"\"energy\":{energy}," ++
    "\"top\":[" ++ kStr ++ "]}"
  IO.println json
