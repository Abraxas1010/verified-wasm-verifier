/-
Copyright (c) 2026 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

import HeytingLean.HeytingVeil.Routing.Core
import Lean.Data.Json

/-!
# Extraction Adapter Registry

Declarative registry for extraction adapters and scaffold helpers.
-/

namespace HeytingLean
namespace HeytingVeil
namespace Extract

open HeytingLean.HeytingVeil.Routing

structure ExtractionAdapter where
  name : String
  inputType : String
  outputType : String
  transportTheorem : String
  supportedBackends : List BackendClass
  description : String
  deriving Repr, Inhabited

def backendTag : BackendClass → String
  | .c => "c"
  | .highIRC => "highir-c"
  | .wasmMini => "wasm"
  | .pythonFFI => "python"
  | .solidity => "solidity"

def adapterToJson (a : ExtractionAdapter) : Lean.Json :=
  Lean.Json.mkObj
    [ ("name", Lean.Json.str a.name)
    , ("input_type", Lean.Json.str a.inputType)
    , ("output_type", Lean.Json.str a.outputType)
    , ("transport_theorem", Lean.Json.str a.transportTheorem)
    , ("supported_backends", Lean.Json.arr <| a.supportedBackends.map (fun b => Lean.Json.str (backendTag b)) |>.toArray)
    , ("description", Lean.Json.str a.description)
    ]

def registry : List ExtractionAdapter :=
  [ { name := "lambdanat_add1"
    , inputType := "Nat"
    , outputType := "Nat"
    , transportTheorem := "HeytingLean.HeytingVeil.Extract.Examples.NatFragmentAdapter.add1Bridge"
    , supportedBackends := [.c, .highIRC, .wasmMini, .pythonFFI, .solidity]
    , description := "LambdaNat increment adapter with proof-carrying transport."
    }
  , { name := "nat2_add2"
    , inputType := "Nat × Nat"
    , outputType := "Nat"
    , transportTheorem := "HeytingLean.HeytingVeil.Extract.Examples.Nat2FragmentAdapter.add2Bridge"
    , supportedBackends := [.c, .highIRC, .wasmMini, .pythonFFI, .solidity]
    , description := "Nat2 add-two-inputs adapter with proof-carrying transport."
    }
  , { name := "minicc_abs"
    , inputType := "MiniC(x)"
    , outputType := "Int"
    , transportTheorem := "HeytingLean.HeytingVeil.MiniCMachine.Examples.AbsVal.absReturnNonnegative"
    , supportedBackends := [.c, .highIRC, .wasmMini, .pythonFFI, .solidity]
    , description := "MiniC abs adapter with bounded non-negativity safety checks."
    }
  , { name := "minicc_clamp"
    , inputType := "MiniC(x,lo,hi)"
    , outputType := "Int"
    , transportTheorem := "HeytingLean.HeytingVeil.MiniCMachine.Examples.Clamp.clampWithinBounds"
    , supportedBackends := [.c, .highIRC, .wasmMini, .pythonFFI, .solidity]
    , description := "MiniC clamp adapter with bounded range safety checks."
    }
  , { name := "minicc_sum_to"
    , inputType := "MiniC(n)"
    , outputType := "Int"
    , transportTheorem := "HeytingLean.HeytingVeil.MiniCMachine.Examples.SumLoop.sumLoopInvariant"
    , supportedBackends := [.c, .highIRC, .wasmMini, .pythonFFI, .solidity]
    , description := "MiniC sum_to adapter with loop-invariant and refinement-loop checks."
    }
  , { name := "minicc_array_sum"
    , inputType := "MiniC(arr)"
    , outputType := "Int"
    , transportTheorem := "HeytingLean.HeytingVeil.MiniCMachine.Examples.Arrays.arraySumWithinBounds"
    , supportedBackends := [.c, .highIRC, .wasmMini, .pythonFFI, .solidity]
    , description := "MiniC array sum adapter with array-bounds-safe verification checks."
    }
  , { name := "minicc_array_max"
    , inputType := "MiniC(arr)"
    , outputType := "Int"
    , transportTheorem := "HeytingLean.HeytingVeil.MiniCMachine.Examples.Arrays.arrayMaxWithinBounds"
    , supportedBackends := [.c, .highIRC, .wasmMini, .pythonFFI, .solidity]
    , description := "MiniC array max adapter with bounds-safe indexed access checks."
    }
  , { name := "minicc_struct_pair_sum"
    , inputType := "MiniC(struct p{x,y})"
    , outputType := "Int"
    , transportTheorem := "HeytingLean.HeytingVeil.MiniCMachine.Properties.VarInRange"
    , supportedBackends := [.c, .highIRC, .wasmMini, .pythonFFI, .solidity]
    , description := "MiniC struct field update/access adapter (flattened slot encoding)."
    }
  , { name := "minicc_call_abs"
    , inputType := "MiniC(call abs_inner)"
    , outputType := "Int"
    , transportTheorem := "HeytingLean.HeytingVeil.Refinement.CompilationRefinement.miniCToCStepRefinementCheck"
    , supportedBackends := [.c, .highIRC, .wasmMini, .pythonFFI, .solidity]
    , description := "MiniC call adapter for bounded stack/call-target safety checks."
    }
  ]

def registryJson : Lean.Json :=
  Lean.Json.arr <| registry.map adapterToJson |>.toArray

def findAdapter? (name : String) : Option ExtractionAdapter :=
  registry.find? (fun a => a.name = name)

private def parseBackendsCsv (csv : String) : List String :=
  csv.splitOn "," |>.map String.trim |>.filter (fun s => !s.isEmpty)

def scaffoldTemplate (name inputType backendsCsv : String) : String :=
  let backendTags := parseBackendsCsv backendsCsv
  let backendList :=
    if backendTags.isEmpty then
      "[]"
    else
      "[" ++ String.intercalate ", " (backendTags.map (fun s => "\"" ++ s ++ "\"")) ++ "]"
  String.intercalate "\n"
    [ "/- Auto-generated HeytingVeil adapter scaffold -/"
    , "import HeytingLean.HeytingVeil.Extract.Core"
    , ""
    , "namespace HeytingLean"
    , "namespace HeytingVeil"
    , "namespace Extract"
    , "namespace Scaffolds"
    , ""
    , s!"-- Adapter name: {name}"
    , s!"-- Input type: {inputType}"
    , s!"-- Declared backends: {backendList}"
    , ""
    , s!"def {name}_spec : String :="
    , s!"  \"SPEC_PLACEHOLDER: formal spec for {name}\""
    , ""
    , s!"theorem {name}_transport : True := by"
    , "  trivial"
    , ""
    , "end Scaffolds"
    , "end Extract"
    , "end HeytingVeil"
    , "end HeytingLean"
    ]

end Extract
end HeytingVeil
end HeytingLean
