import Lean
import Lean.Data.Json
import HeytingLean.CLI.Certified.Json
import HeytingLean.Certified.Export

open Lean
open System
open HeytingLean.CLI.Certified
open HeytingLean.Certified

private def findValue? (flag : String) : List String → Option String
  | [] => none
  | x :: xs =>
      match xs with
      | [] => none
      | y :: _ =>
          if x == flag then some y else findValue? flag xs

def main (args : List String) : IO UInt32 := do
  let outDir := (findValue? "--out" args).getD "out/lof-lib"
  let which := (findValue? "--which" args).getD "demo"
  let lib? : Option CertifiedLibrary :=
    if which == "demo" then
      some CertifiedLibrary.demo
    else if which == "crypto" then
      some CertifiedLibrary.crypto
    else if which == "all" then
      some CertifiedLibrary.all
    else
      none
  match lib? with
  | none =>
      die s!"unknown --which {which} (expected demo|crypto|all)"
  | some lib =>
      try
        Export.writeLibrary lib outDir
        okJson <| Json.mkObj [("ok", Json.bool true), ("out", Json.str outDir), ("which", Json.str which)]
      catch e =>
        die s!"export_library failed: {e}"
