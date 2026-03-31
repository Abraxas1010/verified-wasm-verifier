/-
Copyright (c) 2026 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

import HeytingLean.HeytingVeil.Routing.Core
import HeytingLean.MiniC.ToC
import HeytingLean.MiniC.ToWasmMini
import HeytingLean.MiniC.Syntax
import HeytingLean.C.Syntax
import HeytingLean.WasmMini.Syntax

/-!
# Routing Derivation Hooks

Concrete backend-derivation hooks keyed by `Routing.BackendClass`.
-/

namespace HeytingLean
namespace HeytingVeil
namespace Routing

open HeytingLean.MiniC

/-- Backend-specific artifact produced from a MiniC function. -/
inductive BackendArtifact
  | cFun (f : HeytingLean.C.CFun)
  | wasmFun (f : HeytingLean.WasmMini.Fun)
  | highIRCStub (f : MiniC.Fun)
  | pythonStub (f : HeytingLean.C.CFun)
  | solidityContract (f : HeytingLean.C.CFun)

/-- Derive backend artifact from MiniC according to selected backend class. -/
def deriveFromMiniC (backend : BackendClass) (fn : MiniC.Fun) : BackendArtifact :=
  match backend with
  | .c => .cFun (MiniC.ToC.compileFun fn)
  | .wasmMini => .wasmFun (MiniC.ToWasmMini.compileFun fn)
  | .highIRC => .highIRCStub fn
  | .pythonFFI => .pythonStub (MiniC.ToC.compileFun fn)
  | .solidity => .solidityContract (MiniC.ToC.compileFun fn)

/-- Route-indexed backend derivation wrapper. -/
def deriveFromRoute (route : Route) (fn : MiniC.Fun) : BackendArtifact :=
  deriveFromMiniC route.backend fn

@[simp] theorem deriveFromRoute_backend (route : Route) (fn : MiniC.Fun) :
    deriveFromRoute route fn = deriveFromMiniC route.backend fn := rfl

/-- Stable artifact-kind tag for packaging/export envelopes. -/
def artifactKind : BackendArtifact → String
  | .cFun _ => "c_fun"
  | .wasmFun _ => "wasm_fun"
  | .highIRCStub _ => "highir_c_stub"
  | .pythonStub _ => "python_stub"
  | .solidityContract _ => "solidity_contract"

end Routing
end HeytingVeil
end HeytingLean
