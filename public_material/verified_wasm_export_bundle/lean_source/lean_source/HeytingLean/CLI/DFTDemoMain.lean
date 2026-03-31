import Lean
import Mathlib.Data.Complex.Basic

private def parseArg (xs : List String) (flag : String) : Option String :=
  match xs with
  | [] => none
  | x::y::rest => if x = flag then some y else parseArg (y::rest) flag
  | _ => none

private def parseList (s : String) : Array Float :=
  let parts := s.splitOn ","
  parts.foldl (init := #[]) (fun acc t =>
    match t.toInt? with
    | some v => acc.push (Float.ofInt v)
    | none   => acc)

noncomputable def main (argv : List String) : IO Unit := do
  let n := (parseArg argv "--N").bind (·.toNat?) |>.getD 8
  if n = 0 then
    IO.eprintln "N must be > 0"; IO.Process.exit 1
  -- values default: 0..N-1
  let xs := (parseArg argv "--x").map parseList |>.getD (Array.range n |>.map (fun i => (Float.ofNat i)))
  let len := xs.size
  if len ≠ n then
    IO.eprintln s!"length(x)={len} does not match N={n}"; IO.Process.exit 1
  -- compute DFT directly (small N)
  if n ≠ 4 then
    IO.eprintln "This demo supports N=4 only (fast, no trig)."; IO.Process.exit 1
  let x0 := xs[0]!; let x1 := xs[1]!; let x2 := xs[2]!; let x3 := xs[3]!
  -- ω = exp(-2π i /4) = -i; pattern-based DFT
  let X0r := x0 + x1 + x2 + x3; let X0i := 0.0
  let X2r := x0 - x1 + x2 - x3; let X2i := 0.0
  let X1r := x0 - x2;         let X1i := -(x1) + x3
  let X3r := x0 - x2;         let X3i :=  (x1) - x3
  let specArr : Array String := #[
      s!"[{X0r}, {X0i}]",
      s!"[{X1r}, {X1i}]",
      s!"[{X2r}, {X2i}]",
      s!"[{X3r}, {X3i}]" ]
  -- inverse using 1/4 and conjugate pattern
  let x0' := (X0r + X1r + X2r + X3r) / 4.0
  let x1' := (X0r - X2r + (X3i - X1i)) / 4.0
  let x2' := (X0r - X1r + X2r - X3r) / 4.0
  let x3' := (X0r - X2r + (X1i - X3i)) / 4.0
  let reconArr : Array String := #[(s!"{x0'}"), (s!"{x1'}"), (s!"{x2'}"), (s!"{x3'}")]
  let spec := specArr
  let recon := reconArr
  let nodes := String.intercalate "," (spec.toList)
  let recs := String.intercalate "," (recon.toList)
  let json := "{" ++
    s!"\"N\":{n}," ++
    "\"spectrum\":[" ++ nodes ++ "]," ++
    "\"recon\":[" ++ recs ++ "]}"
  IO.println json
