/-
Copyright (c) 2026 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

/-!
# HeytingVeil Routing Core

Dynamic IR->backend route selection surface, intentionally lightweight:
- classify incoming IR family,
- select backend route by policy/default,
- emit stable route labels for packaging/provenance.
-/

namespace HeytingLean
namespace HeytingVeil
namespace Routing

/-- High-level IR families currently surfaced by HeytingVeil. -/
inductive IRClass
  | lambdaNat
  | lambdaNat2
  | miniCCore
  | generic
  deriving DecidableEq, Repr

/-- Backend language classes used by current export lanes. -/
inductive BackendClass
  | c
  | wasmMini
  | highIRC
  | pythonFFI
  | solidity
  deriving DecidableEq, Repr

/-- Route record selected for downstream packaging. -/
structure Route where
  ir : IRClass
  backend : BackendClass
  deriving Repr

/-- Default backend policy by IR class. -/
def defaultBackend : IRClass → BackendClass
  | .lambdaNat => .c
  | .lambdaNat2 => .c
  | .miniCCore => .c
  | .generic => .wasmMini

/-- Select route from IR class and optional preferred backend override. -/
def selectRoute (ir : IRClass) (preferred? : Option BackendClass := none) : Route where
  ir := ir
  backend := preferred?.getD (defaultBackend ir)

@[simp] theorem selectRoute_ir (ir : IRClass) (preferred? : Option BackendClass := none) :
    (selectRoute ir preferred?).ir = ir := rfl

@[simp] theorem selectRoute_backend_default (ir : IRClass) :
    (selectRoute ir).backend = defaultBackend ir := rfl

/-- Stable string label for audit artifacts. -/
def routeLabel : Route → String
  | ⟨.lambdaNat, .c⟩ => "LambdaNat->MiniC->C"
  | ⟨.lambdaNat, .solidity⟩ => "LambdaNat->MiniC->Solidity"
  | ⟨.lambdaNat2, .c⟩ => "LambdaNat2->MiniC->C"
  | ⟨.lambdaNat2, .solidity⟩ => "LambdaNat2->MiniC->Solidity"
  | ⟨.miniCCore, .c⟩ => "MiniC->C"
  | ⟨.miniCCore, .wasmMini⟩ => "MiniC->WasmMini"
  | ⟨.miniCCore, .highIRC⟩ => "MiniC->HighIRC"
  | ⟨.miniCCore, .pythonFFI⟩ => "MiniC->Python"
  | ⟨.miniCCore, .solidity⟩ => "MiniC->Solidity"
  | ⟨.generic, .wasmMini⟩ => "Generic->WasmMini"
  | ⟨.generic, .solidity⟩ => "Generic->Solidity"
  | ⟨ir, backend⟩ => s!"{reprStr ir}->{reprStr backend}"

end Routing
end HeytingVeil
end HeytingLean
