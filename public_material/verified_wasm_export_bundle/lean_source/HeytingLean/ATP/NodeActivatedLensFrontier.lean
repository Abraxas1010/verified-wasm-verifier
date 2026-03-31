import Lean.Data.Json
import HeytingLean.ATP.ProofNetwork

/-!
# ATP.NodeActivatedLensFrontier

Lean-certified frontier-opening semantics for ATP proof-network nodes.

The goal of this module is modest and explicit:

- define the small kernel-checked contract for when a node activates new search frontiers,
- classify the kinds of openings that can be emitted,
- derive those openings from certified proof-network evidence,
- and prove basic invariants that downstream tooling can rely on.

The Python/tooling layer may adapt repo proof-tree nodes into this summary shape, but
the opening kinds and their construction live here.
-/

namespace HeytingLean
namespace ATP

open Lean
open HeytingLean.Embeddings

/-- Stable opening kinds emitted by the node-activated frontier. -/
inductive FrontierOpeningKind where
  | continueSameLens
  | transportToLens
  | clearObstructionInLens
  | generalizeInvariant
  deriving DecidableEq, Repr

def FrontierOpeningKind.tag : FrontierOpeningKind → String
  | .continueSameLens => "continue_same_lens"
  | .transportToLens => "transport_to_lens"
  | .clearObstructionInLens => "clear_obstruction_in_lens"
  | .generalizeInvariant => "generalize_invariant"

/--
Compact certified summary exposed to the node-activated frontier logic.

This is the intended interface boundary:
- Lean owns the meaning of these fields,
- scripts may populate them from proof-tree / proof-network artifacts,
- frontier activation is computed from this summary, not ad hoc string policy.
-/
structure NodeActivationSummary where
  nodeId : Nat
  currentLens : LensID
  theoremName : String := ""
  transportTargets : List LensID := []
  obstructionClass : Option String := none
  suggestedLenses : List LensID := []
  sheafWitnesses : List String := []
  replayScriptPresent : Bool := false
  deriving Repr

def NodeActivationSummary.hasTheoremSignal (s : NodeActivationSummary) : Bool :=
  !s.theoremName.trim.isEmpty

def NodeActivationSummary.hasWitnessSignal (s : NodeActivationSummary) : Bool :=
  !s.sheafWitnesses.isEmpty

def NodeActivationSummary.hasGeneralizationSignal (s : NodeActivationSummary) : Bool :=
  s.hasTheoremSignal || s.hasWitnessSignal || s.replayScriptPresent

def NodeActivationSummary.hasObstructionSignal (s : NodeActivationSummary) : Bool :=
  match s.obstructionClass with
  | some cls => !cls.trim.isEmpty
  | none => false

/-- A concrete frontier opening emitted from a certified node summary. -/
structure FrontierOpening where
  kind : FrontierOpeningKind
  targetLens : LensID
  reason : String
  witnessRefs : List String := []
  deriving Repr, DecidableEq

instance : Inhabited FrontierOpeningKind where
  default := .continueSameLens

instance : Inhabited NodeActivationSummary where
  default :=
    { nodeId := 0
      currentLens := .omega }

instance : Inhabited FrontierOpening where
  default :=
    { kind := .continueSameLens
      targetLens := .omega
      reason := "" }

def FrontierOpening.kindTag (o : FrontierOpening) : String :=
  o.kind.tag

def continueOpening (s : NodeActivationSummary) : FrontierOpening where
  kind := .continueSameLens
  targetLens := s.currentLens
  reason := "node_certified"
  witnessRefs := if s.hasTheoremSignal then [s.theoremName] else []

def transportOpenings (s : NodeActivationSummary) : List FrontierOpening :=
  ((s.transportTargets.eraseDups).filter (· != s.currentLens)).map fun dst =>
    { kind := .transportToLens
      targetLens := dst
      reason := "transport_trace_certified"
      witnessRefs := if s.hasTheoremSignal then [s.theoremName] else [] }

def obstructionOpenings (s : NodeActivationSummary) : List FrontierOpening :=
  match s.obstructionClass with
  | none => []
  | some cls =>
      if cls.trim.isEmpty then
        []
      else
        ((s.suggestedLenses.eraseDups).filter (· != s.currentLens)).map fun dst =>
          { kind := .clearObstructionInLens
            targetLens := dst
            reason := cls
            witnessRefs := [cls] }

def generalizationOpenings (s : NodeActivationSummary) : List FrontierOpening :=
  if s.hasGeneralizationSignal then
    [{ kind := .generalizeInvariant
       targetLens := s.currentLens
       reason := "witness_or_theorem_signal"
       witnessRefs := (if s.hasTheoremSignal then [s.theoremName] else []) ++ s.sheafWitnesses }]
  else
    []

/--
Authoritative node-activated frontier.

The returned list is intentionally small and structured:
1. always keep a same-lens continuation,
2. add certified transport branches,
3. add obstruction-clearing reroutes when a blocker is explicit,
4. add one generalization branch when theorem/witness evidence exists.
-/
def activateFrontier (s : NodeActivationSummary) : List FrontierOpening :=
  continueOpening s
    :: (transportOpenings s ++ obstructionOpenings s ++ generalizationOpenings s)

def activationCount (s : NodeActivationSummary) : Nat :=
  (activateFrontier s).length

/-- Keep only direct outgoing transfers from the node's current lens. -/
def directTransportTargets (lens : LensID) (trace : List LensTransfer) : List LensID :=
  (trace.filter fun hop => hop.source == lens).map (·.target)

/-- Build a frontier summary from a certified proof-network node, when possible. -/
def summaryOfProofNode? (n : ProofNode) : Option NodeActivationSummary :=
  match n.outcome with
  | .proved artifact =>
      some {
        nodeId := n.id
        currentLens := n.lens
        theoremName := artifact.theoremName
        transportTargets := directTransportTargets n.lens artifact.transportTrace
        sheafWitnesses := artifact.sheafWitnesses
        replayScriptPresent := artifact.replayScript.isSome
      }
  | .blockedCertified cert =>
      some {
        nodeId := n.id
        currentLens := n.lens
        obstructionClass := some cert.obstructionClass
        suggestedLenses := cert.suggestedLenses
      }
  | _ => none

theorem continueOpening_target (s : NodeActivationSummary) :
    (continueOpening s).targetLens = s.currentLens := by
  rfl

theorem continue_mem_activateFrontier (s : NodeActivationSummary) :
    continueOpening s ∈ activateFrontier s := by
  simp [activateFrontier]

theorem activateFrontier_nonempty (s : NodeActivationSummary) :
    (activateFrontier s).length > 0 := by
  simp [activateFrontier]

theorem mem_transportOpenings_target_ne_current
    {s : NodeActivationSummary} {o : FrontierOpening}
    (h : o ∈ transportOpenings s) :
    o.targetLens ≠ s.currentLens := by
  unfold transportOpenings at h
  rcases List.mem_map.mp h with ⟨dst, hdst, rfl⟩
  simp at hdst
  exact hdst.2

theorem mem_obstructionOpenings_target_ne_current
    {s : NodeActivationSummary} {o : FrontierOpening}
    (h : o ∈ obstructionOpenings s) :
    o.targetLens ≠ s.currentLens := by
  unfold obstructionOpenings at h
  cases hcls : s.obstructionClass with
  | none =>
      simp [hcls] at h
  | some cls =>
      by_cases hempty : cls.trim.isEmpty
      · simp [hcls, hempty] at h
      · simp [hcls, hempty] at h
        rcases h with ⟨dst, hdst, rfl⟩
        exact hdst.2

theorem mem_generalizationOpenings_target_eq_current
    {s : NodeActivationSummary} {o : FrontierOpening}
    (h : o ∈ generalizationOpenings s) :
    o.targetLens = s.currentLens := by
  unfold generalizationOpenings at h
  by_cases hs : s.hasGeneralizationSignal
  · simp [hs] at h
    rcases h with rfl
    rfl
  · simp [hs] at h

theorem transport_openings_empty_of_no_targets
    (s : NodeActivationSummary)
    (h : s.transportTargets = []) :
    transportOpenings s = [] := by
  simp [transportOpenings, h]

theorem obstruction_openings_empty_of_no_signal
    (s : NodeActivationSummary)
    (h : s.hasObstructionSignal = false) :
    obstructionOpenings s = [] := by
  unfold NodeActivationSummary.hasObstructionSignal at h
  unfold obstructionOpenings
  cases hcls : s.obstructionClass with
  | none =>
      simp
  | some cls =>
      simp [hcls] at h
      simp [h]

theorem generalization_openings_empty_of_no_signal
    (s : NodeActivationSummary)
    (h : s.hasGeneralizationSignal = false) :
    generalizationOpenings s = [] := by
  simp [generalizationOpenings, h]

theorem summaryOfProofNode?_none_of_inProgress
    (n : ProofNode) (h : n.outcome = .inProgress) :
    summaryOfProofNode? n = none := by
  simp [summaryOfProofNode?, h]

theorem summaryOfProofNode?_none_of_failed
    (n : ProofNode) (msg : String) :
    summaryOfProofNode? { n with outcome := .failed msg } = none := by
  simp [summaryOfProofNode?]

def lensName : LensID → String
  | .omega => "omega"
  | .region => "region"
  | .graph => "graph"
  | .clifford => "clifford"
  | .tensor => "tensor"
  | .topology => "topology"
  | .matula => "matula"

def lensFromString? (s : String) : Option LensID :=
  match s.trim.toLower with
  | "omega" => some .omega
  | "region" => some .region
  | "graph" => some .graph
  | "clifford" => some .clifford
  | "tensor" => some .tensor
  | "topology" => some .topology
  | "matula" => some .matula
  | _ => none

def summaryToJson (s : NodeActivationSummary) : Json :=
  Json.mkObj
    [ ("node_id", Json.num s.nodeId)
    , ("current_lens", Json.str (lensName s.currentLens))
    , ("theorem_name", Json.str s.theoremName)
    , ("transport_targets", Json.arr <| s.transportTargets.toArray.map (fun l => Json.str (lensName l)))
    , ("obstruction_class",
        match s.obstructionClass with
        | some cls => Json.str cls
        | none => Json.null)
    , ("suggested_lenses", Json.arr <| s.suggestedLenses.toArray.map (fun l => Json.str (lensName l)))
    , ("sheaf_witnesses", Json.arr <| s.sheafWitnesses.toArray.map Json.str)
    , ("replay_script_present", Json.bool s.replayScriptPresent)
    ]

def openingToJson (o : FrontierOpening) : Json :=
  Json.mkObj
    [ ("kind", Json.str o.kindTag)
    , ("target_lens", Json.str (lensName o.targetLens))
    , ("reason", Json.str o.reason)
    , ("witness_refs", Json.arr <| o.witnessRefs.toArray.map Json.str)
    ]

def activationToJson (s : NodeActivationSummary) : Json :=
  let openings := activateFrontier s
  Json.mkObj
    [ ("summary", summaryToJson s)
    , ("openings", Json.arr <| openings.toArray.map openingToJson)
    , ("counts",
        Json.mkObj
          [ ("total", Json.num openings.length)
          , ("transport", Json.num (transportOpenings s).length)
          , ("obstruction_clear", Json.num (obstructionOpenings s).length)
          , ("generalization", Json.num (generalizationOpenings s).length)
          ])
    ]

end ATP
end HeytingLean
