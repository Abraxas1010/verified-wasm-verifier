import HeytingLean.LeanCP.Lang.CEmit
import HeytingLean.LeanCP.Compile.SKYLowering

/-!
# LeanCP C Export CLI

Exports LeanCP `CProgramDecl` values as concrete `.c` source files.
Currently supports the SKY reducer lowering surface.

Usage: `lake exe leancp_export [--output <path>] [--no-header]`
-/

open HeytingLean.LeanCP
open HeytingLean.LeanCP.CEmit
open HeytingLean.LeanCP.Compile.SKYLowering

structure ExportCfg where
  output : Option System.FilePath := none
  includeHeader : Bool := true

def parseCfg (args : List String) : ExportCfg :=
  go args {}
where
  go : List String → ExportCfg → ExportCfg
  | [], cfg => cfg
  | "--output" :: path :: rest, cfg => go rest { cfg with output := some path }
  | "-o" :: path :: rest, cfg => go rest { cfg with output := some path }
  | "--no-header" :: rest, cfg => go rest { cfg with includeHeader := false }
  | _ :: rest, cfg => go rest cfg

def main (args : List String) : IO UInt32 := do
  let cfg := parseCfg args
  let src := programDecl skyReducerProgram (includeHeader := cfg.includeHeader)
  match cfg.output with
  | some path =>
      IO.FS.writeFile path src
      IO.println s!"Wrote {src.length} bytes to {path}"
  | none =>
      IO.print src
  return 0
