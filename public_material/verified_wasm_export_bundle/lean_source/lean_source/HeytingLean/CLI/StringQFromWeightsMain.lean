import HeytingLean.Physics.String.VOAGraded
import HeytingLean.Physics.String.ModularQ
import HeytingLean.Physics.String.Examples.IsingQ

namespace HeytingLean
namespace CLI

open HeytingLean.Physics.String
open HeytingLean.Physics.String.Examples.IsingQ

def parseWeights (s : String) : Array Nat :=
  let parts := s.split (· = ',')
  Id.run do
    let mut out : Array Nat := #[]
    for p in parts do
      match p.trim.toNat? with
      | some n => out := out.push n
      | none   => out := out
    out

def StringQFromWeights.run (args : List String) : IO Unit := do
  let weightsStr := args.findSome? (fun a => if a.startsWith "--weights=" then some (a.drop 10) else none) |>.getD "0"
  let steps    := args.findSome? (fun a => if a.startsWith "--steps=" then some (a.drop 8) else none) |>.getD "6"
  let stepsN   := (steps.trim.toNat?).getD 6
  let ws : Array Nat := parseWeights weightsStr
  let G : VOAGraded Unit := { weights := ws }
  let q := VOAGraded.charTrunc G
  let N : QNucleus := { mats := mats, steps := stepsN }
  let canon := (QNucleus.project N q).coeffs
  IO.println s!"weights={ws} -> q={q.coeffs} canonical={canon}"

end CLI
end HeytingLean

def main (args : List String) : IO Unit :=
  HeytingLean.CLI.StringQFromWeights.run args

