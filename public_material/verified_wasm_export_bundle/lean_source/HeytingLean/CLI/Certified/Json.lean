import Lean
import Lean.Data.Json
import Std

namespace HeytingLean
namespace CLI
namespace Certified

open Lean
open Std

def die (msg : String) : IO UInt32 := do
  IO.eprintln msg
  pure 1

def okJson (j : Json) : IO UInt32 := do
  IO.println j.compress
  pure 0

def readInputJson (args : List String) : IO (Except String Json) := do
  let useStdin := args.contains "--stdin"
  let inFile :=
    match args with
    | _ :: "--input" :: f :: _ => some f
    | _ => none
  let input ←
    match inFile with
    | some f => IO.FS.readFile f
    | none =>
        if useStdin then
          (do
            let h ← IO.getStdin
            h.readToEnd)
        else
          pure "{}"
  match Json.parse input with
  | .ok j => pure (.ok j)
  | .error e => pure (.error s!"json error: {e}")

def getString? (j : Json) (k : String) : Option String :=
  match j.getObjVal? k with
  | .ok (.str s) => some s
  | _ => none

def getNat? (j : Json) (k : String) : Option Nat :=
  match j.getObjVal? k with
  | .ok v =>
      match v.getNat? with
      | .ok n => some n
      | .error _ => none
  | .error _ => none

def getInt? (j : Json) (k : String) : Option Int :=
  match j.getObjVal? k with
  | .ok v =>
      match v.getInt? with
      | .ok i => some i
      | .error _ => none
  | .error _ => none

end Certified
end CLI
end HeytingLean
