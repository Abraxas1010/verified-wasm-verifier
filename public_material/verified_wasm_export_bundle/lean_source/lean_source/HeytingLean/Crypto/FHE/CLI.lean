import Lean
import HeytingLean.Crypto.FHE.API

open Lean (Json)

open IO

open HeytingLean.Crypto.FHE.API

def main (args : List String) : IO UInt32 := do
  try
    let useStdin := args.contains "--stdin"
    let inFile := Id.run <|
      match args with
      | _ :: "--input" :: f :: _ => some f
      | _ => none
    let input ← match inFile with
      | some f => do IO.FS.readFile f
      | none => if useStdin then readAllStdin else pure "{\"cmd\":\"keygen\"}"
    match Json.parse input with
    | .ok j =>
        let out ← handle j
        IO.println (out.compress)
        pure 0
    | .error e =>
        IO.println ((Json.mkObj [("error", Json.str s!"json error: {e}")]).compress)
        pure 1
  catch e =>
    IO.println ((Json.mkObj [("error", Json.str (toString e))]).compress)
    pure 1
