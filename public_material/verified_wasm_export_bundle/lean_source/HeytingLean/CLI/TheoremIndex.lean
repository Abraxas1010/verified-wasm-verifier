import Lean.Data.Json
import HeytingLean.PCC.API
import HeytingLean.CLI.Args
import HeytingLean.Theorems.Core
import HeytingLean.Theorems.Cert

open HeytingLean
open HeytingLean.PCC
open Lean
open System

private def usage : String :=
  "theorem_index --list [--category CAT] [--kind KIND] | --list-cert [--category CAT] [--kind KIND] | --get NAME | --get-cert NAME"

structure ListOpts where
  category? : Option String := none
  kind?     : Option String := none

private def runList (cert : Bool) (opts : ListOpts) : IO UInt32 := do
  let cmd := if cert then "list_certified_theorems" else "list_theorems"
  let fields : List (String × Json) :=
    [("command", Json.str cmd)]
      ++ (match opts.category? with
          | some c => [("category", Json.str c)]
          | none => [])
      ++ (match opts.kind? with
          | some k => [("kind", Json.str k)]
          | none => [])
  let out ← evalRequest (Json.mkObj fields)
  IO.println out.pretty
  pure 0

private def runGet (cert : Bool) (name : String) : IO UInt32 := do
  let cmd := if cert then "get_certified_theorem" else "get_theorem"
  let out ← evalRequest (Json.mkObj [("command", Json.str cmd), ("name", Json.str name)])
  IO.println out.pretty
  pure 0

private def parseFilters : List String → Option ListOpts
  | [] => some {}
  | "--category" :: c :: rest =>
      parseFilters rest |>.map (fun o => { o with category? := some c })
  | "--kind" :: k :: rest =>
      parseFilters rest |>.map (fun o => { o with kind? := some k })
  | _ => none

def main (args : List String) : IO UInt32 := do
  let args := HeytingLean.CLI.stripLakeArgs args
  match args with
  | [] =>
      IO.eprintln usage
      pure 0
  | "--list" :: rest =>
      match parseFilters rest with
      | some opts => runList false opts
      | none => IO.eprintln usage; pure 1
  | "--list-cert" :: rest =>
      match parseFilters rest with
      | some opts => runList true opts
      | none => IO.eprintln usage; pure 1
  | ["--get", name] => runGet false name
  | ["--get-cert", name] => runGet true name
  | ["--help"] =>
      IO.eprintln usage
      pure 0
  | _ =>
      IO.eprintln usage
      pure 1
