/-
Copyright (c) 2026 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

import HeytingLean.HeytingVeil.Packaging.Examples.EmittedArtifactRecord
import HeytingLean.HeytingVeil.Packaging.Serialize

/-!
# Packaging Emitter Core

External emitter shims over serialized artifact envelopes.
No side effects are executed here; this defines a typed emission plan surface.
-/

namespace HeytingLean
namespace HeytingVeil
namespace Packaging
namespace Emitter

open HeytingLean.HeytingVeil.Packaging.Examples
open HeytingLean.HeytingVeil.Routing

private def quote (s : String) : String :=
  "\"" ++ s ++ "\""

inductive EmissionTarget
  | stdout
  | filePath (path : String)
  deriving Repr

structure EmissionJob where
  specId : String
  route : String
  payload : String
  target : EmissionTarget
  deriving Repr

private def emissionTargetLabel : EmissionTarget → String
  | .stdout => "stdout"
  | .filePath path => "file:" ++ path

private def renderTarget (target : EmissionTarget) : String :=
  quote (emissionTargetLabel target)

/-- Build an emission job from an emitted artifact record and chosen target. -/
def buildJob (record : EmittedArtifactRecord) (target : EmissionTarget) : EmissionJob where
  specId := record.cert.specId
  route := routeLabel record.route
  payload := emittedArtifactEnvelope record
  target := target

/-- Human-readable command-plan string for out-of-Lean emitters. -/
def renderPlan (job : EmissionJob) : String :=
  match job.target with
  | .stdout =>
      s!"emit[{job.specId}] route={job.route} -> stdout"
  | .filePath path =>
      s!"emit[{job.specId}] route={job.route} -> file:{path}"

/-- Machine-readable emission-job payload for downstream packaging layers. -/
def serializeJob (job : EmissionJob) : String :=
  "{" ++
    "\"specId\":" ++ quote job.specId ++ "," ++
    "\"route\":" ++ quote job.route ++ "," ++
    "\"payload\":" ++ job.payload ++ "," ++
    "\"target\":" ++ renderTarget job.target ++
  "}"

theorem buildJob_route_consistent (record : EmittedArtifactRecord) (target : EmissionTarget) :
    (buildJob record target).route = record.cert.route := by
  simpa [buildJob] using record.route_consistent.symm

end Emitter
end Packaging
end HeytingVeil
end HeytingLean
