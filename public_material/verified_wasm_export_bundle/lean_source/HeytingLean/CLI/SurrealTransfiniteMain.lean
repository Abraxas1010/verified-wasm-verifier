import Lean
import Lean.Data.Json
import HeytingLean.Numbers.Ordinal.Notation
import HeytingLean.Numbers.Surreal.TransfinitePreGame

/-!
# Surreal transfinite birthday demo CLI

This executable is a small, self-contained demonstration that the repository can
compute **transfinite ordinal birthdays** (below ε₀) for a compactly-presented class
of pre-games, including the canonical example `ω = {0,1,2,... | }`.

No args: print a JSON summary and exit 0.
-/

namespace HeytingLean.CLI.SurrealTransfiniteMain

open Lean
open HeytingLean.Numbers.Ordinal
open HeytingLean.Numbers.Surreal.TransfinitePreGame

private def demoJson : Json :=
  let ω := OrdinalCNF.omega
  let ω1 := ω + OrdinalCNF.ofNat 1
  let ω2 := ω + ω
  Json.mkObj
    [ ("version", Json.str "SurrealTransfiniteDemo.v1")
    , ("omega", Json.str (toString ω))
    , ("omega_plus_1", Json.str (toString ω1))
    , ("omega_times_2", Json.str (toString ω2))
    , ("birth_omega", Json.str (toString (birth PreGame.omega)))
    , ("birth_omega_plus_1", Json.str (toString (birth (PreGame.omegaPlusNat 1))))
    , ("birth_omega_times_2", Json.str (toString (birth (.cut .omegaPlusNats (.finite [])))))
    ]

def main (_args : List String) : IO UInt32 := do
  IO.println demoJson.pretty
  pure 0

end HeytingLean.CLI.SurrealTransfiniteMain

open HeytingLean.CLI.SurrealTransfiniteMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.SurrealTransfiniteMain.main args
