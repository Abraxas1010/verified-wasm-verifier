import HeytingLean.Numbers.Surreal.NormalizedPG
import HeytingLean.Numbers.SurrealCore
import Std
import HeytingLean.Util.Iterate

namespace HeytingLean
namespace CLI

open HeytingLean.Numbers
open HeytingLean.Numbers.SurrealCore
open HeytingLean.Numbers.Surreal

/-- One stabilization step: project to canonical rep (currently identity). -/
def stabilizeStep (g : PreGame) : PreGame :=
  SurrealCore.canonicalize g

/-- Iterate stabilization `k` times (library helper). -/
def stabilizeK (k : Nat) (g : PreGame) : PreGame :=
  HeytingLean.Util.iterateN k stabilizeStep g

/-- Tiny demo input: `0`, `1 := {0|}`, and `-1 := {|0}`. -/
def zero : PreGame := PreGame.build [] []
def one : PreGame := PreGame.build [zero] []
def negOne : PreGame := PreGame.build [] [zero]

structure Args where
  steps : Nat := 1
  json : Bool := false

def parseArgs (args : List String) : IO Args := do
  -- Very small parser: --steps N (defaults to 1), --json flag
  let rec go (as : List String) (st : Args) :=
    match as with
    | [] => st
    | "--steps" :: n :: tl =>
        match n.toNat? with
        | some k => go tl { st with steps := k }
        | none => go tl st
    | "--json" :: tl => go tl { st with json := true }
    | _ :: tl => go tl st
  pure <| go args {}

def describe (name : String) (g : PreGame) : String :=
  s!"{name}: birth={g.birth} L={g.L.length} R={g.R.length}"

def runDemoText (steps : Nat) : IO Unit := do
  let inputs : List (String × PreGame) :=
    [("zero", zero), ("one", one), ("negOne", negOne)]
  IO.println s!"SurrealPGNorm — stabilize k={steps} (canonicalize-only demo)"
  for (nm, g) in inputs do
    let g' := stabilizeK steps g
    let taken := steps
    let stabilized := false
    IO.println (describe nm g)
    IO.println (describe s!"{nm}'" g')
    IO.println s!"  stabilized={stabilized} stepsTaken={taken}"

def jsonEscape (s : String) : String :=
  -- minimal escape for our input set; adequate for demo names
  s.replace "\"" "\\\""

def runDemoJson (steps : Nat) : IO Unit := do
  let inputs : List (String × PreGame) :=
    [("zero", zero), ("one", one), ("negOne", negOne)]
  let lines := inputs.map (fun (nm, g) =>
    let g' := stabilizeK steps g
    let taken := steps
    let stabilized := false
    let before := s!"\"birth\":{g.birth},\"L\":{g.L.length},\"R\":{g.R.length}"
    let after := s!"\"birth\":{g'.birth},\"L\":{g'.L.length},\"R\":{g'.R.length}"
    let st := if stabilized then "true" else "false"
    "{" ++
      "\"name\":\"" ++ jsonEscape nm ++ "\"," ++
      "\"k\":" ++ toString steps ++ "," ++
      "\"before\":{" ++ before ++ "}," ++
      "\"after\":{" ++ after ++ "}," ++
      "\"stabilized\":" ++ st ++ "," ++
      "\"stepsTaken\":" ++ toString taken ++
    "}")
  let payload := s!"[{String.intercalate "," lines}]"
  IO.println payload

def SurrealPGNorm.main : IO Unit := do
  -- Fallback: default args when CLI argv is unavailable on this toolchain
  let args : Args := {}
  if args.json then
    runDemoJson args.steps
  else
    runDemoText args.steps

end CLI
end HeytingLean

def main : IO Unit :=
  HeytingLean.CLI.SurrealPGNorm.main
