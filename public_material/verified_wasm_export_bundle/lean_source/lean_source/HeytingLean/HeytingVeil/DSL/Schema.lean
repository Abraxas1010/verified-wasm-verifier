import HeytingLean.HeytingVeil.DSL.Syntax

namespace HeytingLean.HeytingVeil.DSL

structure Profile where
  requireSafety : Bool := true
  requireLiveness : Bool := true
  requireInvariant : Bool := false
  requireReachable : Bool := false
  requireExplicitCoreClauses : Bool := false
  allowFairnessAsLiveness : Bool := true
  allowEmptyState : Bool := true
  allowedBackendHints : List String :=
    [ "lambdair_minic_c"
    , "lambdair_only"
    , "minic_only"
    , "lambdair_highir_c"
    , "lambdair_highir_cpp"
    , "lambdair_highir_rust"
    ]
  allowedBackendTargets : List String := ["c", "cpp", "rust", "minic", "lambdair"]
  deriving Repr, DecidableEq

structure ElaboratedModule where
  parsed : ParsedModule
  profile : Profile
  profileChecks : List String
  deriving Repr, DecidableEq

def defaultProfile : Profile := {}

def conforms (p : Profile) (m : Module) : Bool :=
  let safetyOk := (!p.requireSafety) || (!m.safety.isEmpty)
  let fairnessSupportsLiveness :=
    p.allowFairnessAsLiveness && ((!m.wfActions.isEmpty) || (!m.sfActions.isEmpty) || (!m.reachable.isEmpty))
  let liveEvidence := (!m.liveness.isEmpty) || fairnessSupportsLiveness
  let liveOk := (!p.requireLiveness) || liveEvidence
  let invOk := (!p.requireInvariant) || (!m.invariants.isEmpty)
  let reachOk := (!p.requireReachable) || (!m.reachable.isEmpty)
  let explicitOk :=
    (!p.requireExplicitCoreClauses) ||
      (m.explicitSafetyCount > 0 &&
        ((m.explicitLivenessCount > 0) || fairnessSupportsLiveness) &&
        m.explicitInvariantCount > 0 &&
        m.explicitReachableCount > 0)
  let stateOk := p.allowEmptyState || (!m.stateVars.isEmpty)
  let backendOk := p.allowedBackendHints.contains m.backendHint
  let targetOk := p.allowedBackendTargets.contains m.backendTarget
  safetyOk && liveOk && invOk && reachOk && explicitOk && stateOk && backendOk && targetOk

def elaborate (p : Profile) (pm : ParsedModule) : Except String ElaboratedModule :=
  if conforms p pm.mod then
    .ok { parsed := pm, profile := p, profileChecks := ["conforms"] }
  else
    .error s!"profile conformance failed for module {pm.mod.name}"

/--
Sprint proof obligation `HV.DSL.SchemaConformant` for the core path.
-/
theorem schemaConformant_of_elaborate_ok
    {p : Profile} {pm : ParsedModule} {em : ElaboratedModule}
    (h : elaborate p pm = .ok em) :
    conforms p pm.mod = true := by
  unfold elaborate at h
  by_cases hc : conforms p pm.mod
  · simp [hc] at h
    simp [hc]
  · simp [hc] at h

end HeytingLean.HeytingVeil.DSL
