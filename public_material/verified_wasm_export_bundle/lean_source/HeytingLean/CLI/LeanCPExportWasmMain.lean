import HeytingLean.LeanCP.Lang.WasmEmit
import HeytingLean.LeanCP.Lang.CToWasm
import HeytingLean.LeanCP.Compile.SKYLowering

/-!
# LeanCP WebAssembly Export CLI

Exports LeanCP `CProgramDecl` values as WebAssembly Text Format (`.wat`)
files by translating the C IR to Wasm IR and emitting WAT text.

Usage: `lake exe leancp_export_wasm [--output <path>]`
-/

open HeytingLean.LeanCP
open HeytingLean.LeanCP.Wasm.Emit
open HeytingLean.LeanCP.CToWasm
open HeytingLean.LeanCP.Compile.SKYLowering

structure ExportCfg where
  output : Option System.FilePath := none

def parseCfg (args : List String) : ExportCfg :=
  go args {}
where
  go : List String → ExportCfg → ExportCfg
  | [], cfg => cfg
  | "--output" :: path :: rest, cfg => go rest { cfg with output := some path }
  | "-o" :: path :: rest, cfg => go rest { cfg with output := some path }
  | _ :: rest, cfg => go rest cfg

def main (args : List String) : IO UInt32 := do
  let cfg := parseCfg args
  let wasmMod := translateModule skyReducerProgram
  let src := moduleDecl wasmMod
  match cfg.output with
  | some path =>
      IO.FS.writeFile path src
      IO.println s!"Wrote {src.length} bytes to {path}"
  | none =>
      IO.print src
  return 0
