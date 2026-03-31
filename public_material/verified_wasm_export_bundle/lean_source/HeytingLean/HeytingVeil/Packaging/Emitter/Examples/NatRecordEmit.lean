/-
Copyright (c) 2026 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

import HeytingLean.HeytingVeil.Packaging.Emitter.Core

/-!
# Nat Record Emit Examples

Concrete emission jobs built from existing nat and nat2 bridge records.
-/

namespace HeytingLean
namespace HeytingVeil
namespace Packaging
namespace Emitter
namespace Examples

open HeytingLean.HeytingVeil.Packaging.Examples
open HeytingLean.HeytingVeil.Extract.Examples
open HeytingLean.HeytingVeil.Routing

private def backendFileTag : BackendClass → String
  | BackendClass.c => "c"
  | BackendClass.wasmMini => "wasm"
  | BackendClass.pythonFFI => "python"
  | BackendClass.highIRC => "highirc"
  | BackendClass.solidity => "solidity"

private def backendDefaultPath (name : String) (n : Nat) (backend : BackendClass) : String :=
  s!"artifacts/heytingveil/{name}_{n}_" ++ backendFileTag backend ++ ".json"

private def backendDefaultPath2 (name : String) (x y : Nat) (backend : BackendClass) : String :=
  s!"artifacts/heytingveil/{name}_{x}_{y}_" ++ backendFileTag backend ++ ".json"

def add1FileJob (n : Nat) : EmissionJob :=
  buildJob (emitNatRecord add1Bridge n) (.filePath s!"artifacts/heytingveil/add1_{n}.json")

def add2StdoutJob (x y : Nat) : EmissionJob :=
  buildJob (emitNat2Record add2Bridge x y) .stdout

theorem add1FileJob_route_matches_cert (n : Nat) :
    (add1FileJob n).route = (emitNatRecord add1Bridge n).cert.route := by
  exact buildJob_route_consistent _ _

theorem add2StdoutJob_route_matches_cert (x y : Nat) :
    (add2StdoutJob x y).route = (emitNat2Record add2Bridge x y).cert.route := by
  exact buildJob_route_consistent _ _

def add2HighIRCFileJob (x y : Nat) : EmissionJob :=
  buildJob (emitNat2RecordWithPreference add2Bridge x y (some Routing.BackendClass.highIRC)) (.filePath s!"artifacts/heytingveil/add2_{x}_{y}_highirc.json")

theorem add2HighIRCFileJob_route_matches_cert (x y : Nat) :
    (add2HighIRCFileJob x y).route =
      (emitNat2RecordWithPreference add2Bridge x y (some Routing.BackendClass.highIRC)).cert.route := by
  exact buildJob_route_consistent _ _

def add1HighIRCFileJob (n : Nat) : EmissionJob :=
  buildJob (emitNatRecordWithPreference add1Bridge n (some Routing.BackendClass.highIRC)) (.filePath s!"artifacts/heytingveil/add1_{n}_highirc.json")

theorem add1HighIRCFileJob_route_matches_cert (n : Nat) :
    (add1HighIRCFileJob n).route =
      (emitNatRecordWithPreference add1Bridge n (some Routing.BackendClass.highIRC)).cert.route := by
  exact buildJob_route_consistent _ _

def add1WasmFileJob (n : Nat) : EmissionJob :=
  buildJob (emitNatRecordWithPreference add1Bridge n (some BackendClass.wasmMini))
    (.filePath (backendDefaultPath "add1" n BackendClass.wasmMini))

def add1PythonFileJob (n : Nat) : EmissionJob :=
  buildJob (emitNatRecordWithPreference add1Bridge n (some BackendClass.pythonFFI))
    (.filePath (backendDefaultPath "add1" n BackendClass.pythonFFI))

def add2WasmFileJob (x y : Nat) : EmissionJob :=
  buildJob (emitNat2RecordWithPreference add2Bridge x y (some BackendClass.wasmMini))
    (.filePath (backendDefaultPath2 "add2" x y BackendClass.wasmMini))

def add2PythonFileJob (x y : Nat) : EmissionJob :=
  buildJob (emitNat2RecordWithPreference add2Bridge x y (some BackendClass.pythonFFI))
    (.filePath (backendDefaultPath2 "add2" x y BackendClass.pythonFFI))

def add1SolidityFileJob (n : Nat) : EmissionJob :=
  buildJob (emitNatRecordWithPreference add1Bridge n (some BackendClass.solidity))
    (.filePath (backendDefaultPath "add1" n BackendClass.solidity))

def add2SolidityFileJob (x y : Nat) : EmissionJob :=
  buildJob (emitNat2RecordWithPreference add2Bridge x y (some BackendClass.solidity))
    (.filePath (backendDefaultPath2 "add2" x y BackendClass.solidity))

theorem add1WasmFileJob_route_matches_cert (n : Nat) :
    (add1WasmFileJob n).route =
      (emitNatRecordWithPreference add1Bridge n (some BackendClass.wasmMini)).cert.route := by
  exact buildJob_route_consistent _ _

theorem add1PythonFileJob_route_matches_cert (n : Nat) :
    (add1PythonFileJob n).route =
      (emitNatRecordWithPreference add1Bridge n (some BackendClass.pythonFFI)).cert.route := by
  exact buildJob_route_consistent _ _

theorem add2WasmFileJob_route_matches_cert (x y : Nat) :
    (add2WasmFileJob x y).route =
      (emitNat2RecordWithPreference add2Bridge x y (some BackendClass.wasmMini)).cert.route := by
  exact buildJob_route_consistent _ _

theorem add2PythonFileJob_route_matches_cert (x y : Nat) :
    (add2PythonFileJob x y).route =
      (emitNat2RecordWithPreference add2Bridge x y (some BackendClass.pythonFFI)).cert.route := by
  exact buildJob_route_consistent _ _

theorem add1SolidityFileJob_route_matches_cert (n : Nat) :
    (add1SolidityFileJob n).route =
      (emitNatRecordWithPreference add1Bridge n (some BackendClass.solidity)).cert.route := by
  exact buildJob_route_consistent _ _

theorem add2SolidityFileJob_route_matches_cert (x y : Nat) :
    (add2SolidityFileJob x y).route =
      (emitNat2RecordWithPreference add2Bridge x y (some BackendClass.solidity)).cert.route := by
  exact buildJob_route_consistent _ _

end Examples
end Emitter
end Packaging
end HeytingVeil
end HeytingLean
