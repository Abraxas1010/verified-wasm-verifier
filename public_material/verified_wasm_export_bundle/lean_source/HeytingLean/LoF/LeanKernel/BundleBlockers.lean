import Lean.Data.Json
import HeytingLean.LoF.LeanKernel.BundleCheck

namespace HeytingLean
namespace LoF
namespace LeanKernel

open Lean

private def containsSubstr (hay needle : String) : Bool :=
  match hay.splitOn needle with
  | _ :: _ :: _ => true
  | _ => false

inductive BlockerFamily where
  | exportGap
  | envGap
  | whnfGap
  | recursorGap
  | transportGap
  | performanceGap
  deriving Repr, DecidableEq

def BlockerFamily.code : BlockerFamily → String
  | .exportGap => "export_gap"
  | .envGap => "env_gap"
  | .whnfGap => "whnf_gap"
  | .recursorGap => "recursor_gap"
  | .transportGap => "transport_gap"
  | .performanceGap => "performance_gap"

private def diagnosticText (result : ObligationResult) : String :=
  match result.detail.getObjValAs? String "diagnostic" with
  | .ok s => s
  | _ => ""

def classifyBlocker (result : ObligationResult) : BlockerFamily :=
  let diagnostic := diagnosticText result
  if containsSubstr diagnostic "fuel_exhausted" then
    .performanceGap
  else if containsSubstr diagnostic "const_type_missing" || containsSubstr diagnostic "lit_type_missing" ||
      containsSubstr diagnostic "bvar_out_of_scope" || containsSubstr diagnostic "mvar_type_missing" then
    .envGap
  else if containsSubstr diagnostic "Eq.rec" || containsSubstr diagnostic "Eq.ndrec" || containsSubstr diagnostic "transport" then
    .transportGap
  else if containsSubstr diagnostic "casesOn" || containsSubstr diagnostic "recursor" || containsSubstr diagnostic "below" ||
      containsSubstr diagnostic "brecOn" then
    .recursorGap
  else if containsSubstr diagnostic "defeq_" || containsSubstr diagnostic "not_sort" || result.kind == "whnf" then
    .whnfGap
  else
    .exportGap

def blockerJson (result : ObligationResult) : Json :=
  Json.mkObj
    [ ("label", Json.str result.label)
    , ("kind", Json.str result.kind)
    , ("family", Json.str (classifyBlocker result).code)
    , ("detail", result.detail)
    ]

def blockerCounts (results : List ObligationResult) : Array (String × Nat) :=
  let families := [BlockerFamily.exportGap, .envGap, .whnfGap, .recursorGap, .transportGap, .performanceGap]
  families.toArray.map fun family =>
    (family.code, results.foldl (init := 0) fun acc result =>
      if result.status == .blocked && classifyBlocker result == family then acc + 1 else acc)

end LeanKernel
end LoF
end HeytingLean
