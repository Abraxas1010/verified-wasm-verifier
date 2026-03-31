import Lean.Data.Json
import HeytingLean.LoF.ICC.Encoder.Classifier

namespace HeytingLean
namespace LoF
namespace ICC
namespace Encoder

open Lean

structure ICCEnvironmentSummary where
  closureSize : Nat
  closureOverflow : Bool
  missingDependencyCount : Nat
  axiomDeps : Array String
  opaqueDeps : Array String
  recursorDeps : Array String
  trustAssumptions : Array String
  deriving Repr

private def closureBucket (env : Environment) (summary : DeclSummary) :
    Array String × Array String × Array String :=
  summary.closure.foldl
    (init := (#[], #[], #[]))
    (fun (axioms, opaques, recursors) dep =>
      match env.find? dep with
      | some (.axiomInfo _) => (axioms.push dep.toString, opaques, recursors)
      | some (.opaqueInfo _) => (axioms, opaques.push dep.toString, recursors)
      | some (.recInfo _) => (axioms, opaques, recursors.push dep.toString)
      | _ => (axioms, opaques, recursors))

private def baseTrustAssumptions (summary : DeclSummary) : List String :=
  let missing :=
    if summary.missingDeps.isEmpty then [] else ["missing_dependency"]
  let truncated :=
    if summary.closureOverflow then ["closure_truncated"] else []
  missing ++ truncated

def summarizeICCEnvironment (env : Environment) (summary : DeclSummary)
    (classification : DeclClassification) : ICCEnvironmentSummary :=
  let (axiomDeps, opaqueDeps, recursorDeps) := closureBucket env summary
  let trust :=
    (baseTrustAssumptions summary ++ classification.trustAssumptions).eraseDups.toArray.qsort (· < ·)
  { closureSize := summary.closure.size
    closureOverflow := summary.closureOverflow
    missingDependencyCount := summary.missingDeps.size
    axiomDeps := axiomDeps.qsort (· < ·)
    opaqueDeps := opaqueDeps.qsort (· < ·)
    recursorDeps := recursorDeps.qsort (· < ·)
    trustAssumptions := trust }

def iccEnvironmentJson (info : ICCEnvironmentSummary) : Json :=
  Json.mkObj
    [ ("closure_size", toJson info.closureSize)
    , ("closure_overflow", Json.bool info.closureOverflow)
    , ("missing_dependency_count", toJson info.missingDependencyCount)
    , ("axiom_deps", Json.arr <| info.axiomDeps.map Json.str)
    , ("opaque_deps", Json.arr <| info.opaqueDeps.map Json.str)
    , ("recursor_deps", Json.arr <| info.recursorDeps.map Json.str)
    , ("trust_assumptions", Json.arr <| info.trustAssumptions.map Json.str)
    ]

end Encoder
end ICC
end LoF
end HeytingLean
