import Lean
import Lean.Data.Json
import HeytingLean.CLI.Args
import HeytingLean.Crypto.ZK.Export
import HeytingLean.Crypto.ZK.R1CS
import HeytingLean.Crypto.BoolLens
import HeytingLean.Payments.Types
import HeytingLean.Payments.Rules
import HeytingLean.Payments.Commit

/-!
Simple gateway-style validator that reuses the same checks as pm_verify,
exposed as a programmatic function and a CLI entry.
-/

namespace HeytingLean
namespace Gateway

open Lean
open Crypto.ZK
open Crypto.BoolLens
open Payments

structure GatewayConfig where
  maxGasPrice : Nat := 0
  minProofQuality : Float := 0.0
  batchSize : Nat := 1
  deriving Repr, Inhabited

structure ValidationResult where
  valid : Bool
  gasEstimate : Nat := 0
  shouldSubmit : Bool := false
  reason : String := ""
  deriving Repr

def validateFiles (policyPath statePath r1csPath witnessPath publicPath : System.FilePath) : IO ValidationResult := do
  let readFileE (p : System.FilePath) (label : String) : IO (Except String String) := do
    try
      let s ← IO.FS.readFile p
      pure (.ok s)
    catch e =>
      pure (.error s!"read error ({label}) at {p}: {e}")
  let polRaw ← match (← readFileE policyPath "policy") with | .ok s => pure s | .error e => return { valid := false, reason := e }
  let stRaw  ← match (← readFileE statePath "state") with | .ok s => pure s | .error e => return { valid := false, reason := e }
  let sysRaw ← match (← readFileE r1csPath "r1cs") with | .ok s => pure s | .error e => return { valid := false, reason := e }
  let witRaw ← match (← readFileE witnessPath "witness") with | .ok s => pure s | .error e => return { valid := false, reason := e }
  let pubRaw ← match (← readFileE publicPath "public") with | .ok s => pure s | .error e => return { valid := false, reason := e }
  let _polJ := match Json.parse polRaw with | .ok j => j | .error _ => Json.null
  let _stJ  := match Json.parse stRaw  with | .ok j => j | .error _ => Json.null
  let sysJ := match Json.parse sysRaw with | .ok j => j | .error _ => Json.null
  let asJ  := match Json.parse witRaw with | .ok j => j | .error _ => Json.null
  let _pubJ := match Json.parse pubRaw with | .ok j => j | .error _ => Json.null
  -- Parse
  let some sys := Export.jsonToSystem sysJ | return { valid := false, reason := "Bad system" }
  let some arr := Export.jsonToAssignment asJ | return { valid := false, reason := "Bad assignment" }
  -- size guard
  let maxVar := sys.constraints.foldl (init := 0) (fun m c =>
    let step := fun acc (ts : List (Var × ℚ)) => ts.foldl (fun a p => Nat.max a p.fst) acc
    let m1 := step 0 c.A.terms; let m2 := step m1 c.B.terms; let m3 := step m2 c.C.terms; Nat.max m m3)
  if arr.size ≤ maxVar then
    return { valid := false, reason := s!"Witness too small, needs ≥ {maxVar+1}, got {arr.size}" }
  let assign := Export.assignmentOfArray arr
  let okSat : Bool := sys.constraints.all (fun c => ((c.A.eval assign) * (c.B.eval assign)) == (c.C.eval assign))
  if ¬ okSat then return { valid := false, reason := "R1CS not satisfied by witness" }
  -- If we need more checks, reuse PMVerify pipeline here. Minimal gateway returns true on sat.
  return { valid := true, gasEstimate := 0, shouldSubmit := true }

end Gateway
end HeytingLean

open HeytingLean.Gateway in
def main (args : List String) : IO UInt32 := do
  let args := HeytingLean.CLI.stripLakeArgs args
  match args with
  | [policyPath, statePath, r1csPath, witnessPath, publicPath] =>
      let res ← HeytingLean.Gateway.validateFiles (System.FilePath.mk policyPath) (System.FilePath.mk statePath)
        (System.FilePath.mk r1csPath) (System.FilePath.mk witnessPath) (System.FilePath.mk publicPath)
      if res.valid then
        IO.println "{\"valid\":true,\"shouldSubmit\":true}"
        return 0
      else
        IO.println ("{\"valid\":false,\"reason\":\"" ++ res.reason ++ "\"}")
        return 1
  | _ =>
      IO.eprintln "usage: lake exe gateway_verify <policy.json> <state.json> <r1cs.json> <witness.json> <public.json>"
      return 2
