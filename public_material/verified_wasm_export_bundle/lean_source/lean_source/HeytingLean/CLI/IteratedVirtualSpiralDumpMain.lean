import HeytingLean.IteratedVirtual.Spiral
import HeytingLean.Compiler.TensorLogic.ParseFacts

/-!
# CLI.IteratedVirtualSpiralDumpMain

Emit a small JSON array of helix points. Designed to succeed with no args so Dev Mode QA
can run it as a smoke test.

Options (all optional):
- `--n <Nat>` number of steps (default: 32)
- `--step <Float>` angular step (default: 0.35)
- `--pitch <Float>` z pitch per radian (default: 0.15)
- `--help`
-/

namespace HeytingLean.CLI.IteratedVirtualSpiralDumpMain

open HeytingLean.IteratedVirtual
open Lean

private def parseNatArg (argv : List String) (flag : String) : Option Nat :=
  match argv.dropWhile (fun s => s != flag) with
  | _ :: v :: _ => String.toNat? v
  | _ => none

private def parseFloatArg (argv : List String) (flag : String) : Option Float :=
  match argv.dropWhile (fun s => s != flag) with
  | _ :: v :: _ =>
      match HeytingLean.Compiler.TensorLogic.parseFloatLit v with
      | .ok f => some f
      | .error _ => none
  | _ => none

private def usage : String :=
  String.intercalate "\n"
    [ "iterated_virtual_spiral_dump"
    , ""
    , "Emits a JSON array of helix points."
    , ""
    , "Options:"
    , "  --n <Nat>       number of steps (default: 32)"
    , "  --step <Float>  angular step (default: 0.35)"
    , "  --pitch <Float> z pitch per radian (default: 0.15)"
    , "  --help"
    ]

def main (argv : List String) : IO UInt32 := do
  if argv.contains "--help" then
    IO.println usage
    return 0

  let n := (parseNatArg argv "--n").getD 32
  let step := (parseFloatArg argv "--step").getD 0.35
  let pitch := (parseFloatArg argv "--pitch").getD 0.15

  let pts := HeytingLean.IteratedVirtual.embedSteps n step pitch
  let out := Json.arr <| (pts.map Point3.toJson |>.toArray)
  IO.println (Json.pretty out)
  return 0

end HeytingLean.CLI.IteratedVirtualSpiralDumpMain

def main (argv : List String) : IO UInt32 :=
  HeytingLean.CLI.IteratedVirtualSpiralDumpMain.main argv
