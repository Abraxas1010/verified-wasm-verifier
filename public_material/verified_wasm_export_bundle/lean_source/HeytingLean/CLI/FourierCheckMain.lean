import Lean
import HeytingLean.Analysis.DFTFloat
import HeytingLean.CLI.Args

namespace HeytingLean.CLI.FourierCheckMain

open Lean

structure Args where
  x : Option String := none
  y : Option String := none
  tolDen : Nat := 1000
deriving Inhabited

private def parseArgs (argv : List String) : Except String Args :=
  let rec go (st : Args) : List String → Except String Args
    | [] => .ok st
    | "--x" :: v :: rest => go { st with x := some v } rest
    | "--y" :: v :: rest => go { st with y := some v } rest
    | "--tolDen" :: v :: rest =>
        match v.toNat? with
        | some n => go { st with tolDen := n } rest
        | none => .error "bad --tolDen (expected Nat)"
    | tok :: rest =>
        if tok.startsWith "--x=" then
          go { st with x := some (tok.drop 4) } rest
        else if tok.startsWith "--y=" then
          go { st with y := some (tok.drop 4) } rest
        else if tok.startsWith "--tolDen=" then
          match (tok.drop 9).toNat? with
          | some n => go { st with tolDen := n } rest
          | none => .error "bad --tolDen=... (expected Nat)"
        else
          go st rest
  go ({} : Args) argv

private def parseIntArray (raw : String) : Except String (Array Float) := do
  let parts := raw.splitOn "," |>.map (·.trim) |>.filter (· ≠ "")
  if parts.isEmpty then
    .error "empty vector"
  else
    let rec go (xs : List String) (acc : Array Float) : Except String (Array Float) :=
      match xs with
      | [] => .ok acc
      | p :: ps =>
          match p.toInt? with
          | some i => go ps (acc.push (Float.ofInt i))
          | none => .error s!"bad int '{p}'"
    go parts #[]

private def circConv (x y : Array Float) : Array Float := Id.run do
  let n := x.size
  let mut out := Array.replicate n 0.0
  for i in [0:n] do
    let mut s : Float := 0.0
    for k in [0:n] do
      let j := (i + n - k) % n
      s := s + x[k]! * y[j]!
    out := out.set! i s
  return out

private def cmul (a b : Float × Float) : Float × Float :=
  let (ar, ai) := a
  let (br, bi) := b
  (ar * br - ai * bi, ar * bi + ai * br)

private def usage : String :=
  String.intercalate "\n"
    [ "fourier_check"
    , ""
    , "Checks the circular convolution theorem (Float DFT):"
    , "  DFT(x ⋆ y)[k] ≈ DFT(x)[k] * DFT(y)[k]"
    , ""
    , "Usage:"
    , "  fourier_check --x 1,0,-1,0 --y 0,1,0,-1 --tolDen 1000"
    , ""
    , "Inputs are comma-separated integers (converted to Float)."
    ]

def run (argv : List String) : IO Unit := do
  let argv := HeytingLean.CLI.stripLakeArgs argv
  if argv.contains "--help" || argv.contains "-h" then
    IO.println usage
    return

  let args ←
    match parseArgs argv with
    | .ok a => pure a
    | .error msg =>
        IO.eprintln msg
        IO.Process.exit 1

  let xRaw := args.x.getD ""
  let yRaw := args.y.getD ""
  if xRaw = "" || yRaw = "" then
    IO.eprintln "missing --x or --y"
    IO.Process.exit 1
  if args.tolDen = 0 then
    IO.eprintln "tolDen must be positive"
    IO.Process.exit 1

  let x ←
    match parseIntArray xRaw with
    | .ok xs => pure xs
    | .error msg =>
        IO.eprintln s!"x: {msg}"
        IO.Process.exit 1
  let y ←
    match parseIntArray yRaw with
    | .ok ys => pure ys
    | .error msg =>
        IO.eprintln s!"y: {msg}"
        IO.Process.exit 1

  if x.size ≠ y.size then
    IO.eprintln "x and y must have the same length"
    IO.Process.exit 1

  let n := x.size
  let conv := circConv x y
  let fx := HeytingLean.Analysis.DFTFloat.dft x
  let fy := HeytingLean.Analysis.DFTFloat.dft y
  let fconv := HeytingLean.Analysis.DFTFloat.dft conv

  let tol : Float := 1.0 / (Float.ofNat args.tolDen)
  let mut maxErrRe : Float := 0.0
  let mut maxErrIm : Float := 0.0
  for k in [0:n] do
    let lhs := fconv[k]!
    let rhs := cmul fx[k]! fy[k]!
    let dr := Float.abs (lhs.1 - rhs.1)
    let di := Float.abs (lhs.2 - rhs.2)
    if dr > maxErrRe then maxErrRe := dr
    if di > maxErrIm then maxErrIm := di

  let maxErr := max maxErrRe maxErrIm
  let ok : Bool := decide (maxErr ≤ tol)

  let json :=
    "{" ++
      "\"kind\":\"fourier_check\"," ++
      s!"\"n\":{n}," ++
      s!"\"tolDen\":{args.tolDen}," ++
      s!"\"tol\":{tol}," ++
      s!"\"maxErrRe\":{maxErrRe}," ++
      s!"\"maxErrIm\":{maxErrIm}," ++
      s!"\"maxErr\":{maxErr}," ++
      s!"\"ok\":{ok}" ++
    "}"
  IO.println json
  if !ok then
    IO.Process.exit 2

end HeytingLean.CLI.FourierCheckMain

def main (argv : List String) : IO Unit :=
  HeytingLean.CLI.FourierCheckMain.run argv
