import Lean
import Lean.Data.Json
import HeytingLean.CLI.Args
import HeytingLean.Crypto.ZK.R1CS
import HeytingLean.Crypto.ZK.Export
import HeytingLean.Crypto.BoolLens
import HeytingLean.Chain.Types

/-!
Minimal verifier core mirroring pm_verify checks, intended to be portable
to an on-chain target in a later stage. Pure Lean, no external deps.
-/

namespace HeytingLean
namespace Chain
namespace Verifier

open Lean
open Crypto.ZK
open Crypto.BoolLens

structure PublicBundle where
  epoch                : Nat
  recipient            : String
  amount               : String
  budget_id            : String
  policyCommitment     : String
  stateCommitment_pre  : String
  stateCommitment_post : String
  nullifier            : String
  output_index         : Nat
  env_indices          : List Nat
  deriving Repr

def parsePublicBundleE (j : Json) : Except String PublicBundle := do
  let getStr (k : String) : Except String String :=
    match j.getObjVal? k with
    | .ok (.str s) => .ok s
    | _ => .error s!"public field '{k}' missing or not string"
  let epoch : Nat := match j.getObjVal? "epoch" with
    | .ok v => (match v.getNat? with | .ok n => n | .error _ => 0)
    | .error _ => 0
  -- parse optional env_indices
  let envIdxs : List Nat :=
    match j.getObjVal? "env_indices" with
    | .ok (.arr a) => a.toList.map (fun jj => match jj.getNat? with | .ok n => n | .error _ => 0)
    | _ => []
  pure {
    epoch := epoch,
    recipient := (← getStr "recipient"),
    amount := (← getStr "amount"),
    budget_id := (← getStr "budget_id"),
    policyCommitment := (← getStr "policyCommitment"),
    stateCommitment_pre := (← getStr "stateCommitment_pre"),
    stateCommitment_post := (← getStr "stateCommitment_post"),
    nullifier := (← getStr "nullifier"),
    output_index :=
      (match j.getObjVal? "output_index" with
       | .ok v => (match v.getNat? with | .ok n => n | .error _ => 0)
       | .error _ => 0),
    env_indices := envIdxs
  }

def verifySystemAndWitness (sysJ asJ : Json) (pubJ : Json) : Except String Bool := do
  let some sys := Export.jsonToSystem sysJ | throw "Bad system JSON"
  let some arr := Export.jsonToAssignment asJ | throw "Bad witness JSON"
  -- Parse public bundle and enforce output_index==1
  let pub ← match parsePublicBundleE pubJ with | .ok p => pure p | .error e => throw e
  -- Extract meta binding from R1CS JSON
  let meta? := match sysJ.getObjVal? "meta" with | .ok m => some m | .error _ => none
  let (metaOut?, metaEnv?) :=
    match meta? with
    | some m =>
        let outi := match m.getObjVal? "output_index" with
          | .ok v => (match (Lean.Json.getNat? v) with | .ok n => some n | .error _ => none)
          | .error _ => none
        let envis := match m.getObjVal? "env_indices" with
          | .ok (.arr a) =>
              let rec go (i : Nat) (acc : List Nat) : Option (List Nat) :=
                if h : i < a.size then
                  have _ := h
                  let e := a[i]!
                  match (Lean.Json.getNat? e) with
                  | .ok n => go (i+1) (n :: acc)
                  | .error _ => none
                else
                  some acc.reverse
              go 0 []
          | _ => none
        (outi, envis)
    | none => (none, none)
  -- Require meta present and equal to public bindings
  match metaOut?, metaEnv? with
  | some mo, some me =>
      if mo ≠ pub.output_index then throw "r1cs.meta.output_index != public.output_index"
      if me ≠ pub.env_indices then throw "r1cs.meta.env_indices != public.env_indices"
  | _, _ => throw "missing r1cs meta bindings"
  -- size sanity
  let maxVar := sys.constraints.foldl (init := 0) (fun m c =>
    let step := fun acc (ts : List (Var × ℚ)) => ts.foldl (fun a p => Nat.max a p.fst) acc
    let m1 := step 0 c.A.terms; let m2 := step m1 c.B.terms; let m3 := step m2 c.C.terms; Nat.max m m3)
  if arr.size ≤ maxVar then throw s!"Witness too small, needs ≥ {maxVar+1}, got {arr.size}"
  -- satisfaction and output==1
  let assign := Export.assignmentOfArray arr
  if !HeytingLean.Chain.checkSatisfaction sys assign then return false
  -- Enforce output_index position equals 1
  let outVal := assign pub.output_index
  if outVal ≠ (1 : ℚ) then return false
  -- Require env_indices present and of expected arity (4)
  if pub.env_indices.length ≠ 4 then throw "public.env_indices must contain 4 indices"
  -- Enforce output equals AND of env booleans (0/1)
  let envVals : List ℚ := pub.env_indices.map (fun i => assign i)
  let envAllOne : Bool := envVals.all (fun v => v = 1)
  let envAnd : ℚ := if envAllOne then 1 else 0
  if outVal ≠ envAnd then return false
  -- Policy shape: a ∧ b ∧ c ∧ d must be true
  let φ :=
    let v (i : Fin 4) := Crypto.Form.var i
    Crypto.Form.and (Crypto.Form.and (v ⟨0, by decide⟩) (v ⟨1, by decide⟩)) (Crypto.Form.and (v ⟨2, by decide⟩) (v ⟨3, by decide⟩))
  -- We recompute env externally in pm_verify; the chain variant is minimal and trusts `sys` encapsulation.
  -- As we cannot recover env here, rely on sys/output equality check via the compiled output var.
  -- Our exporter sets the output as headD of stack; we check it equals 1 in pm_verify.
  -- Here we simply ensure satisfaction; on-chain integration will pass a designated output index.
  return true

end Verifier
end Chain
end HeytingLean

open HeytingLean.Chain.Verifier in
def main (args : List String) : IO UInt32 := do
  let args := HeytingLean.CLI.stripLakeArgs args
  let readFile? (path : String) : IO (Option String) := do
    try
      let s ← IO.FS.readFile (System.FilePath.mk path)
      pure (some s)
    catch e =>
      IO.eprintln s!"read error at {path}: {e}"
      pure none
  match args with
  | [r1csPath, witnessPath, publicPath] =>
      let sysRaw ← match (← readFile? r1csPath) with | some s => pure s | none => return 1
      let witRaw ← match (← readFile? witnessPath) with | some s => pure s | none => return 1
      let pubRaw ← match (← readFile? publicPath) with | some s => pure s | none => return 1
      let sysJ := match Lean.Json.parse sysRaw with | .ok j => j | .error _ => Lean.Json.null
      let asJ  := match Lean.Json.parse witRaw with | .ok j => j | .error _ => Lean.Json.null
      let pubJ := match Lean.Json.parse pubRaw with | .ok j => j | .error _ => Lean.Json.null
      match HeytingLean.Chain.Verifier.verifySystemAndWitness sysJ asJ pubJ with
      | .ok true => IO.println "ok"; return 0
      | .ok false => IO.eprintln "fail"; return 2
      | .error e  => IO.eprintln e; return 1
  | _ =>
      IO.eprintln "usage: lake exe chain_verify <r1cs.json> <witness.json> <public.json>"; return 1
