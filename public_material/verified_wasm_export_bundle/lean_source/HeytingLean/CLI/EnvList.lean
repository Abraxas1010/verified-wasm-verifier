import Lean
import Lean.Data.Json
import HeytingLean.CLI.EnvBootstrap
import HeytingLean.Util.ModuleOwner
open System

open Lean

private def constKind (ci : ConstantInfo) : String :=
  match ci with
  | .thmInfo _     => "theorem"
  | .axiomInfo _   => "axiom_decl"
  | .defnInfo _    => "def"
  | .opaqueInfo _  => "opaque"
  | .quotInfo _    => "quot"
  | .inductInfo _  => "inductive"
  | .ctorInfo _    => "ctor"
  | .recInfo _     => "recursor"

def main (_argv : List String) : IO Unit := do
  HeytingLean.CLI.EnvBootstrap.bootstrapSearchPath
  let env ← importModules #[{module := `Init}, {module := `HeytingLean}] {}
  let mut arr : Array Json := #[]
  for (n, ci) in env.constants.toList do
    if n.toString.startsWith "HeytingLean." then
      let mod :=
        HeytingLean.Util.moduleOwnerOf env n
      let j := Json.mkObj
        [ ("name", Json.str (toString n))
        , ("module", Json.str (toString mod))
        , ("kind", Json.str (constKind ci))
        ]
      arr := arr.push j
  IO.println (toString (Json.arr arr))
