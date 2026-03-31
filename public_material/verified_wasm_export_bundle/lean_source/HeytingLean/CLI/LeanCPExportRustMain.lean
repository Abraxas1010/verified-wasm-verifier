import HeytingLean.LeanCP.Lang.RustEmit
import HeytingLean.LeanCP.Lang.CToRust
import HeytingLean.LeanCP.Compile.SKYLowering

/-!
# LeanCP Rust Export CLI

Exports LeanCP `CProgramDecl` values as concrete `.rs` source files by
translating the C IR to Rust IR and emitting Rust text.

Usage: `lake exe leancp_export_rust [--output <path>]`
-/

open HeytingLean.LeanCP
open HeytingLean.LeanCP.Rust.Emit
open HeytingLean.LeanCP.CToRust
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
  let rustProg := translateProgram skyReducerProgram
  let src := programDecl rustProg
  match cfg.output with
  | some path =>
      IO.FS.writeFile path src
      IO.println s!"Wrote {src.length} bytes to {path}"
  | none =>
      IO.print src
  return 0
