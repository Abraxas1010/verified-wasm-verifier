import Lean
import Lean.Data.Json
import HeytingLean.CLI.Args
import HeytingLean.Meta.LeanTT0.Hash
import HeytingLean.Meta.LeanTT0.Core

/-!
  kernel_commit: emits out/kernel.json with a stable kernelCommitment digest.
  For v0, we hash a canonical kernel descriptor string of TT0 β semantics.
-/

namespace HeytingLean.Meta.LeanTT0.CLI
namespace KernelCommitMain

open HeytingLean.Meta.LeanTT0
open Lean

private def hexOfBA (ba : ByteArray) : String :=
  let parts := ba.toList.map (fun b =>
    let s := (Nat.toDigits 16 b.toNat).asString
    if s.length = 1 then "0" ++ s else s)
  "0x" ++ String.intercalate "" parts

-- Canonical descriptor; bump when semantics change.
private def kernelDescriptor : String :=
  "Kernel:TT0.kernel:v1;rules=[BetaLamApp,DeltaPrimNatAdd];semantics=det"

def main (args : List String) : IO UInt32 := do
  let args := HeytingLean.CLI.stripLakeArgs args
  let rec parseOut (xs : List String) (out : String) : String :=
    match xs with
    | [] => out
    | "--out" :: p :: rest => parseOut rest p
    | tok :: rest =>
        if tok.startsWith "--out=" then
          parseOut rest (tok.drop 6)
        else
          parseOut rest out
  let outDir := parseOut args "out"
  let okMkDir : Bool ← do
    try
      IO.FS.createDirAll outDir
      pure true
    catch e =>
      IO.eprintln s!"E-OUTDIR {e}"
      pure false
  if !okMkDir then
    return 2
  let kc := sha256 (kernelDescriptor.toUTF8)
  let obj := Json.mkObj [("kernelCommitment", Json.str (hexOfBA kc))]
  let p := s!"{outDir}/kernel.json"
  let okWrite : Bool ← do
    try
      IO.FS.writeFile p (Json.compress obj)
      pure true
    catch e =>
      IO.eprintln s!"E-WRITE {e}"
      pure false
  if !okWrite then
    return 2
  IO.println s!"Wrote {p}"
  return 0

end KernelCommitMain
end HeytingLean.Meta.LeanTT0.CLI

def main (args : List String) : IO UInt32 :=
  HeytingLean.Meta.LeanTT0.CLI.KernelCommitMain.main args
