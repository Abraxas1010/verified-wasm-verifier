import Lean.Data.Json
import HeytingLean.ATP.DifferentiableATP.CombToExpr
import HeytingLean.LoF.Combinators.Differential.GradientDescent

/-!
# ATP.DifferentiableATP.OracleEncoder

Lightweight oracle-driven goal encoding:
- probes tactic-table entries against the concrete goal via `lake env lean`,
- caches probe booleans on disk,
- returns `IOExample` rows with success/failure signal.
-/

namespace HeytingLean
namespace ATP
namespace DifferentiableATP

open Lean
open HeytingLean.LoF
open HeytingLean.LoF.Combinators.Differential
open HeytingLean.LoF.Combinators.Differential.Compute

private def sanitizeGoalExpr (goal : String) : String :=
  let g := goal.trim
  if g.startsWith "⊢" then (g.drop 1).trim else g

private def ensureOracleCacheDir : IO System.FilePath := do
  let dir := System.FilePath.mk ".tmp" / "differentiable_atp" / "oracle_cache"
  IO.FS.createDirAll dir
  pure dir

private def cachePath (goal : String) : IO System.FilePath := do
  let dir ← ensureOracleCacheDir
  pure <| dir / s!"oracle_{hash goal}.json"

private def decodeBoolArray (j : Json) : Option (List Bool) :=
  match j with
  | .arr xs =>
      xs.foldr
        (fun x acc =>
          match x, acc with
          | .bool b, some rest => some (b :: rest)
          | _, _ => none)
        (some [])
  | _ => none

private def readCache (goal : String) : IO (Option (List Bool)) := do
  let path ← cachePath goal
  if !(← path.pathExists) then
    return none
  let raw ← IO.FS.readFile path
  match Json.parse raw with
  | .error _ => return none
  | .ok j =>
      let arr? := j.getObjValAs? Json "probe_ok"
      match arr? with
      | .error _ => return none
      | .ok arr =>
          return decodeBoolArray arr

private def writeCache (goal : String) (rows : List Bool) : IO Unit := do
  let path ← cachePath goal
  let payload :=
    Json.mkObj
      [ ("schema", Json.str "differentiable_oracle_cache_v1")
      , ("goal_hash", Json.str s!"{hash goal}")
      , ("probe_ok", Json.arr <| rows.toArray.map Json.bool)
      ]
  IO.FS.writeFile path payload.compress

private def wrapperText (goalExpr tactic : String) : String :=
  String.intercalate "\n"
    [ "import Mathlib"
    , "set_option autoImplicit false"
    , s!"example : {goalExpr} := by"
    , s!"  {tactic}"
    , ""
    ]

private def ensureProbeDir : IO System.FilePath := do
  let dir := System.FilePath.mk ".tmp" / "differentiable_atp" / "oracle_probe"
  IO.FS.createDirAll dir
  pure dir

private def runProbe (goalExpr tactic : String) (idx : Nat) : IO Bool := do
  let dir ← ensureProbeDir
  let tag := hash (goalExpr ++ "|" ++ tactic ++ "|" ++ toString idx)
  let path := dir / s!"probe_{idx}_{tag}.lean"
  IO.FS.writeFile path (wrapperText goalExpr tactic)
  let out ← IO.Process.output
    { cmd := "lake"
      args := #["env", "lean", path.toString]
      cwd := some (System.FilePath.mk ".") }
  pure (out.exitCode == 0)

private def probeAll (goalExpr : String) (tactics : List String) : IO (List Bool) := do
  let rec go (rest : List String) (idx : Nat) (acc : List Bool) : IO (List Bool) := do
    match rest with
    | [] => pure acc.reverse
    | tac :: tail =>
        let ok ← runProbe goalExpr tac idx
        go tail (idx + 1) (ok :: acc)
  go tactics 0 []

private def oracleExamplesFromBooleans (rows : List Bool) : List IOExample :=
  let entries := tacticTable
  let rec go (es : List TacticEntry) (bs : List Bool) (acc : List IOExample) : List IOExample :=
    match es, bs with
    | [], _ => acc.reverse
    | _, [] => acc.reverse
    | e :: et, ok :: bt =>
        let input := single e.pattern 1
        let expected :=
          if ok then
            add (single e.pattern 1) (single .K 1)
          else
            add (single e.pattern (-1)) (single .Y 1)
        go et bt ({ input := input, expected := expected } :: acc)
  go entries rows []

/-- Probe tactic-table entries against a concrete goal and return oracle examples.
    Results are cached on disk per goal hash. -/
def oracleEncode (goal : String) : IO (List IOExample) := do
  let goalExpr := sanitizeGoalExpr goal
  if goalExpr.isEmpty then
    return []
  let expected := tacticTable.length
  match (← readCache goal) with
  | some rows =>
      if rows.length = expected then
        return oracleExamplesFromBooleans rows
      else
        let tactics := tacticTable.map (fun e => e.tactic)
        let fresh ← probeAll goalExpr tactics
        let _ ← writeCache goal fresh
        return oracleExamplesFromBooleans fresh
  | none =>
      let tactics := tacticTable.map (fun e => e.tactic)
      let fresh ← probeAll goalExpr tactics
      let _ ← writeCache goal fresh
      return oracleExamplesFromBooleans fresh

end DifferentiableATP
end ATP
end HeytingLean
