import Lean
import Lean.Data.Json
import HeytingLean.Util.SHA

/-!
# CoqLens — Thin bridge to Coq via SerAPI/Python emitter

Spawns `python3 scripts/coq_emit_cert.py` to emit a translation certificate
(`cert.json`), then parses it and exposes a simple Lean structure.
-/

namespace HeytingLean
namespace Bridges
namespace CoqLens

open Lean

structure Certificate where
  carrierId    : String
  nucleusId    : String
  proofs_rt1   : Bool
  proofs_rt2   : List String
  proofs_triad : Bool
  lemmas       : List String
  publicDigest : String
deriving Repr

namespace Certificate

def ofJson (j : Json) : Except String Certificate := do
  let o ← j.getObj?
  let getStr (k : String) :=
    match o.get? k with | some (.str s) => Except.ok s | _ => Except.error s!"missing string field: {k}"
  let getStrList (k : String) :=
    match o.get? k with
    | some (.arr a) =>
        let acc := a.foldl (fun acc j => match j with | .str s => s :: acc | _ => acc) ([] : List String)
        Except.ok acc.reverse
    | _ => Except.error s!"missing array field: {k}"
  let proofs ←
    match o.get? "proofs" with
    | some (.obj m) => pure m
    | _ => throw s!"missing object field: proofs"
  let rt1 := match proofs.get? "rt1" with | some (.bool b) => b | _ => false
  let rt2 := match proofs.get? "rt2" with | some (.arr a) => a.foldl (fun acc j => match j with | .str s => s :: acc | _ => acc) [] | _ => []
  let tri := match proofs.get? "triad" with | some (.bool b) => b | _ => false
  let carrierId ← getStr "carrier_id"
  let nucleusId ← getStr "nucleus_id"
  let lemmas ← getStrList "lemmas"
  let digest ← getStr "public_digest"
  return { carrierId, nucleusId, proofs_rt1 := rt1, proofs_rt2 := rt2, proofs_triad := tri, lemmas, publicDigest := digest }

end Certificate

private def runEmitter (outPath : System.FilePath) : IO Unit := do
  let cwd ← IO.currentDir
  let scr1 := (cwd / System.FilePath.mk "scripts/coq_emit_cert.py")
  let scr2 := (cwd / System.FilePath.mk "../scripts/coq_emit_cert.py")
  let script := if (← scr1.pathExists) then scr1 else scr2
  let args : Array String := #[script.toString, "--out", outPath.toString]
  let exe := "python3"
  let child ← IO.Process.spawn { cmd := exe, args := args, stdout := .piped, stderr := .piped }
  let wait ← child.wait
  if wait != 0 then
    let err ← child.stderr.readToEnd
    throw <| IO.userError s!"coq emitter failed ({wait}): {err}"
  pure ()

def getCertificate (outPath? : Option System.FilePath := none) : IO Certificate := do
  let out := outPath?.getD (System.FilePath.mk "cert.json")
  -- Ensure parent dir exists
  if let some p := out.parent then
    IO.FS.createDirAll p
  else
    pure ()
  -- Run emitter
  try
    runEmitter out
  catch _ =>
    -- Attempt degraded mode by calling emitter without args; it should default
    runEmitter out
  -- Read and decode
  let s ← IO.FS.readFile out
  let js ←
    match Json.parse s with
    | .ok j => pure j
    | .error e => throw <| IO.userError s!"invalid cert.json: {e}"
  match Certificate.ofJson js with
  | .ok cert => pure cert
  | .error e => throw <| IO.userError e

end CoqLens
end Bridges
end HeytingLean
