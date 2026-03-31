import Lean
import Lean.Data.Json
import HeytingLean.Util.SHA
import HeytingLean.Util.JCS
import HeytingLean.Numbers.SurrealCore
import HeytingLean.Numbers.Surreal.LoFProgram
import HeytingLean.Numbers.Surreal.LensLattice
import HeytingLean.Numbers.Surreal.LensSemantics

/-!
# Bidirectional proof artifacts for surreal LoF programs (toy, executable)

This module implements a *forward/backward* evidence protocol for
surreal pre-game constructions:

- **Forward**: a `LoFProgram.Program` is evaluated to a `PreGame`,
  while recording a step-by-step trace of intermediate nodes.
- **Backward**: a verifier replays the program evaluation, checks
  per-node digests, and returns an explicit confirmation/rejection
  report (with its own digest).

On top of this we provide a minimal **Dialectica-style** interface:

- witness   := forward artifact
- challenge := verification query
- response  := backward verification report

All artifacts are JSON-serializable and hashed with SHA-256 (pure Lean).
The goal is *auditable executables* rather than deep proof theory.
-/

namespace HeytingLean
namespace Numbers
namespace Surreal

open Lean
open HeytingLean.Numbers.SurrealCore
open HeytingLean.Numbers.Surreal.LoFProgram
open HeytingLean.Util

namespace BidirectionalProof

inductive DigestMode where
  | lean
  | jcs
  deriving Repr, DecidableEq

def DigestMode.algString : DigestMode → String
  | .lean => "sha256-lean"
  | .jcs => "sha256-jcs"

def DigestMode.ofAlgString? : String → Option DigestMode
  | "sha256-lean" => some .lean
  | "sha256-jcs" => some .jcs
  -- Legacy (pre-mode) artifacts.
  | "sha256" => some .lean
  | _ => none

/-! ## Hashing helpers -/

def sha256HexString (s : String) : String :=
  SHA256.sha256Hex s.toUTF8

def sha256HexJson (mode : DigestMode) (j : Json) : String :=
  let s :=
    match mode with
    | .lean => j.compress
    | .jcs => HeytingLean.Util.JCS.canonicalString j
  sha256HexString s

/-! ## JSON for pre-games and programs -/

/-! ### Termination helpers for nested `PreGame` recursion -/

private theorem sizeOf_lt_sizeOf_list_of_mem [SizeOf α] {x : α} {xs : List α} (hx : x ∈ xs) :
    sizeOf x < sizeOf xs := by
  induction xs with
  | nil => cases hx
  | cons h t ih =>
      cases hx with
      | head =>
          have hpos : 0 < 1 + sizeOf t := by
            have : 0 < sizeOf t + 1 := Nat.succ_pos _
            simpa [Nat.add_comm] using this
          have hlt : sizeOf x < sizeOf x + (1 + sizeOf t) :=
            Nat.lt_add_of_pos_right hpos
          simpa [List.cons.sizeOf_spec, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlt
      | tail _ hx1 =>
          have hlt : sizeOf x < sizeOf t := ih hx1
          have htpos : 0 < 1 + sizeOf h := by
            have : 0 < sizeOf h + 1 := Nat.succ_pos _
            simpa [Nat.add_comm] using this
          have ht_lt : sizeOf t < sizeOf t + (1 + sizeOf h) :=
            Nat.lt_add_of_pos_right htpos
          have ht_lt' : sizeOf t < sizeOf (h :: t) := by
            simpa [List.cons.sizeOf_spec, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ht_lt
          exact Nat.lt_trans hlt ht_lt'

private theorem sizeOf_lt_sizeOf_pregame_mk_left
    (L R : List PreGame) (birth : Nat) {x : PreGame} (hx : x ∈ L) :
    sizeOf x < sizeOf ({ L := L, R := R, birth := birth } : PreGame) := by
  have hx' : sizeOf x < sizeOf L := sizeOf_lt_sizeOf_list_of_mem hx
  have hpos : 0 < (1 + sizeOf R + sizeOf birth) := by
    have : 0 < Nat.succ (sizeOf R + sizeOf birth) := Nat.succ_pos _
    simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
  have hlt : sizeOf L < sizeOf L + (1 + sizeOf R + sizeOf birth) :=
    Nat.lt_add_of_pos_right hpos
  have hL : sizeOf L < sizeOf ({ L := L, R := R, birth := birth } : PreGame) := by
    simpa [PreGame.mk.sizeOf_spec, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlt
  exact Nat.lt_trans hx' hL

private theorem sizeOf_lt_sizeOf_pregame_mk_right
    (L R : List PreGame) (birth : Nat) {x : PreGame} (hx : x ∈ R) :
    sizeOf x < sizeOf ({ L := L, R := R, birth := birth } : PreGame) := by
  have hx' : sizeOf x < sizeOf R := sizeOf_lt_sizeOf_list_of_mem hx
  have hpos : 0 < (1 + sizeOf L + sizeOf birth) := by
    have : 0 < Nat.succ (sizeOf L + sizeOf birth) := Nat.succ_pos _
    simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
  have hlt : sizeOf R < sizeOf R + (1 + sizeOf L + sizeOf birth) :=
    Nat.lt_add_of_pos_right hpos
  have hR : sizeOf R < sizeOf ({ L := L, R := R, birth := birth } : PreGame) := by
    simpa [PreGame.mk.sizeOf_spec, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlt
  exact Nat.lt_trans hx' hR

def preGameToJson : PreGame → Json
  | { L := L, R := R, birth := birth } =>
      Json.mkObj
        [ ("birth", Json.num birth)
        , ("L", Json.arr <| (L.map preGameToJson).toArray)
        , ("R", Json.arr <| (R.map preGameToJson).toArray)
        ]
termination_by g => sizeOf g
decreasing_by
  all_goals
    first
    | exact sizeOf_lt_sizeOf_pregame_mk_left _ _ _ (by assumption)
    | exact sizeOf_lt_sizeOf_pregame_mk_right _ _ _ (by assumption)

private def getObj (j : Json) : Except String (List (String × Json)) :=
  match j with
  | .obj o => .ok o.toList
  | _ => .error "expected JSON object"

private def getKey (o : List (String × Json)) (k : String) : Except String Json :=
  match o.find? (fun kv => kv.1 == k) with
  | some kv => .ok kv.2
  | none => .error s!"missing key {k}"

private def getNat (j : Json) : Except String Nat :=
  match j.getNat? with
  | .ok n => .ok n
  | .error e => .error s!"expected Nat: {e}"

private def getNatArray (j : Json) : Except String (List Nat) := do
  match j with
  | .arr a =>
      let mut out : List Nat := []
      for x in a.toList do
        let n ← getNat x
        out := n :: out
      return out.reverse
  | _ => throw "expected JSON array"

private def getJsonArray (j : Json) : Except String (List Json) :=
  match j with
  | .arr a => .ok a.toList
  | _ => .error "expected JSON array"

private def preGameOfJsonFuel : Nat → Json → Except String PreGame
  | 0, _ => .error "preGameOfJson: recursion fuel exhausted"
  | Nat.succ fuel, j => do
      let o ← getObj j
      let birth ← getKey o "birth" >>= getNat
      let Ljs ← getKey o "L" >>= getJsonArray
      let Rjs ← getKey o "R" >>= getJsonArray
      let L ← Ljs.mapM (preGameOfJsonFuel fuel)
      let R ← Rjs.mapM (preGameOfJsonFuel fuel)
      return { L := L, R := R, birth := birth }

def preGameOfJson (j : Json) : Except String PreGame :=
  -- Fuel is derived from the serialized JSON length, which is a safe
  -- upper bound for the size of the JSON tree in practice.
  preGameOfJsonFuel (j.compress.length + 1) j

def opToJson : Op → Json
  | .unmark => Json.mkObj [("kind", Json.str "unmark")]
  | .mark L R =>
      Json.mkObj
        [ ("kind", Json.str "mark")
        , ("L", Json.arr <| (L.map (fun (n : Nat) => Json.num (n : JsonNumber))).toArray)
        , ("R", Json.arr <| (R.map (fun (n : Nat) => Json.num (n : JsonNumber))).toArray)
        ]

def programToJson (p : Program) : Json :=
  Json.mkObj
    [ ("ops", Json.arr <| (p.ops.toList.map opToJson).toArray)
    , ("root", Json.num p.root)
    ]

def opOfJson (j : Json) : Except String Op := do
  let o ← getObj j
  let kind ← getKey o "kind"
  match kind with
  | .str "unmark" => return .unmark
  | .str "mark" =>
      let L ← getKey o "L" >>= getNatArray
      let R ← getKey o "R" >>= getNatArray
      return .mark L R
  | _ => throw "unknown op.kind"

def programOfJson (j : Json) : Except String Program := do
  let o ← getObj j
  let opsJ ← getKey o "ops"
  let root ← getKey o "root" >>= getNat
  let opsList ← getJsonArray opsJ
  let ops ← opsList.mapM opOfJson
  return { ops := ops.toArray, root := root }

/-! ## Forward / backward artifacts -/

structure ReferenceToken where
  alg : String := "sha256"
  digest : String
  deriving Repr, DecidableEq

instance : ToJson ReferenceToken where
  toJson t := Json.mkObj [("alg", Json.str t.alg), ("digest", Json.str t.digest)]

structure BidirectionalTokenPair where
  forward : ReferenceToken
  backward : ReferenceToken
  deriving Repr, DecidableEq

instance : ToJson BidirectionalTokenPair where
  toJson p := Json.mkObj [("forward", toJson p.forward), ("backward", toJson p.backward)]

structure ForwardStep where
  idx : Nat
  op : Op
  birth : Nat
  nodeDigest : String
  prevDigest : String
  stepDigest : String
  deriving Repr, DecidableEq

private def forwardStepCoreJson (s : ForwardStep) : Json :=
  Json.mkObj
    [ ("idx", Json.num s.idx)
    , ("op", opToJson s.op)
    , ("birth", Json.num s.birth)
    , ("nodeDigest", Json.str s.nodeDigest)
    , ("prevDigest", Json.str s.prevDigest)
    ]

instance : ToJson ForwardStep where
  toJson s :=
    Json.mkObj
      [ ("idx", Json.num s.idx)
      , ("op", opToJson s.op)
      , ("birth", Json.num s.birth)
      , ("nodeDigest", Json.str s.nodeDigest)
      , ("prevDigest", Json.str s.prevDigest)
      , ("stepDigest", Json.str s.stepDigest)
      ]

structure ForwardArtifact where
  version : String := "SurrealForward.v2"
  lensPath : List LensPoint
  program : Program
  programDigest : String
  nodes : Array PreGame
  root : PreGame
  rootDigest : String
  finalStepDigest : String
  forwardToken : ReferenceToken
  steps : Array ForwardStep
  deriving Repr

private def forwardArtifactToJsonWithTokenDigest (a : ForwardArtifact) (digest : String) : Json :=
  let nodesJson := Json.arr <| (a.nodes.toList.map preGameToJson).toArray
  let stepsJson := Json.arr <| (a.steps.map Lean.toJson)
  let lensJson := Json.arr <| (a.lensPath.map Lean.toJson).toArray
  Json.mkObj
    [ ("version", Json.str a.version)
    , ("lensPath", lensJson)
    , ("program", programToJson a.program)
    , ("programDigest", Json.str a.programDigest)
    , ("nodes", nodesJson)
    , ("root", preGameToJson a.root)
    , ("rootDigest", Json.str a.rootDigest)
    , ("finalStepDigest", Json.str a.finalStepDigest)
    , ("forwardToken", Json.mkObj [("alg", Json.str a.forwardToken.alg), ("digest", Json.str digest)])
    , ("steps", stepsJson)
    ]

def ForwardArtifact.toJson (a : ForwardArtifact) : Json :=
  forwardArtifactToJsonWithTokenDigest a a.forwardToken.digest

structure VerifyQuery where
  version : String := "SurrealVerifyQuery.v1"
  expectedRootDigest : Option String := none
  maxBirth : Option Nat := none
  deriving Repr, DecidableEq

instance : ToJson VerifyQuery where
  toJson q :=
    Json.mkObj <|
      [ ("version", Json.str q.version)
      , ("expectedRootDigest", match q.expectedRootDigest with | none => Json.null | some s => Json.str s)
      , ("maxBirth", match q.maxBirth with | none => Json.null | some n => Json.num n)
      ]

structure VerifyReport where
  version : String := "SurrealVerifyReport.v1"
  ok : Bool
  errors : List String
  verifiedRootDigest : String
  backwardToken : ReferenceToken
  tokenPair : BidirectionalTokenPair
  deriving Repr

instance : ToJson VerifyReport where
  toJson r :=
    Json.mkObj
      [ ("version", Json.str r.version)
      , ("ok", Json.bool r.ok)
      , ("errors", Json.arr <| (r.errors.map Json.str).toArray)
      , ("verifiedRootDigest", Json.str r.verifiedRootDigest)
      , ("backwardToken", toJson r.backwardToken)
      , ("tokenPair", toJson r.tokenPair)
      ]

/-! ## Forward run + backward verification -/

def defaultLensPath : List LensPoint :=
  [ LensPoint.default
  , { sem := .dialectica, comp := .functional, alg := .core }
  , { sem := .dialectica, comp := .functional, alg := .tensor }
  ]

def forward (p : Program) (lensPath : List LensPoint := defaultLensPath) (maxBirth : Option Nat := none)
    (mode : DigestMode := .jcs) :
    Except String ForwardArtifact := do
  -- Validate lens path structurally + semantically.
  match compossiblePathSemantic lensPath with
  | .ok _ => pure ()
  | .error e => throw e

  let programDigest := sha256HexJson mode (programToJson p)

  let nodes ←
    match maxBirth with
    | none => p.evalAll
    | some θ => do
        let nodes ← p.evalAll
        for g in nodes.toList do
          if g.birth > θ then
            throw s!"birthday bound exceeded: birth={g.birth} > θ={θ}"
        pure nodes

  let root ←
    match maxBirth with
    | none => p.eval
    | some θ => p.evalWithMaxBirth θ

  let rootJson := preGameToJson root
  let rootDigest := sha256HexJson mode rootJson

  -- Build a step list (node digests are computed from node JSON).
  let mut steps : Array ForwardStep := #[]
  let mut prev : String := ""
  for h : i in [:nodes.size] do
    let idx : Nat := i
    let op :=
      match p.getOp? idx with
      | some op => op
      | none => Op.unmark
    let g := nodes[i]
    let d := sha256HexJson mode (preGameToJson g)
    let core : ForwardStep :=
      { idx := idx
        op := op
        birth := g.birth
        nodeDigest := d
        prevDigest := prev
        stepDigest := "" }
    let stepDigest := sha256HexJson mode (forwardStepCoreJson core)
    let step : ForwardStep := { core with stepDigest := stepDigest }
    steps := steps.push step
    prev := stepDigest

  let finalStepDigest := prev

  let baseArtifact : ForwardArtifact :=
    { version :=
        match mode with
        | .lean => "SurrealForward.v2"
        | .jcs => "SurrealForward.v3"
      lensPath := lensPath
      program := p
      programDigest := programDigest
      nodes := nodes
      root := root
      rootDigest := rootDigest
      finalStepDigest := finalStepDigest
      forwardToken := { alg := mode.algString, digest := "" }
      steps := steps }

  let forwardDigest := sha256HexJson mode (forwardArtifactToJsonWithTokenDigest baseArtifact "")
  let forwardToken : ReferenceToken := { alg := mode.algString, digest := forwardDigest }
  return { baseArtifact with forwardToken := forwardToken }

def verify (a : ForwardArtifact) (q : VerifyQuery := {}) : VerifyReport :=
  let mode? := DigestMode.ofAlgString? a.forwardToken.alg
  let mode : DigestMode := mode?.getD .lean
  let alg : String :=
    match mode? with
    | some _ => a.forwardToken.alg
    | none => mode.algString
  let errors₀ :=
    (match mode? with
      | none =>
          [s!"unknown forwardToken.alg: {a.forwardToken.alg} (expected sha256-lean or sha256-jcs)"]
      | some _ => [])
    ++
      (match compossiblePathSemantic a.lensPath with
        | .ok _ => []
        | .error e => [e])
    ++
      (let want := sha256HexJson mode (programToJson a.program)
       if want != a.programDigest then
         [s!"programDigest mismatch: expected {want}, got {a.programDigest}"]
       else
         [])
    ++
      (let want := sha256HexJson mode (forwardArtifactToJsonWithTokenDigest a "")
       if want != a.forwardToken.digest then
         [s!"forwardToken mismatch: expected {want}, got {a.forwardToken.digest}"]
       else
         [])

  let nodesE := a.program.evalAll
  let rootE := a.program.eval

  let (nodes?, errors₁) :=
    match nodesE with
    | .ok xs => (some xs, [])
    | .error e => (none, [s!"evalAll failed: {e}"])

  let (root?, errors₂) :=
    match rootE with
    | .ok g => (some g, [])
    | .error e => (none, [s!"eval failed: {e}"])

  let verifiedRootDigest :=
    match root? with
    | none => ""
    | some g => sha256HexJson mode (preGameToJson g)

  let errors₃ :=
    match q.expectedRootDigest with
    | none => []
    | some want =>
        if want != verifiedRootDigest then
          [s!"root digest mismatch: expected {want}, got {verifiedRootDigest}"]
        else
          []

  let errors₄ :=
    match q.maxBirth, nodes? with
    | some θ, some nodes =>
        nodes.toList.foldl
          (fun acc g =>
            if g.birth > θ then
              acc.concat s!"birthday bound exceeded: birth={g.birth} > θ={θ}"
            else
              acc)
          []
    | _, _ => []

  let errors₅ :=
    let storedRootDigest := sha256HexJson mode (preGameToJson a.root)
    (if storedRootDigest != a.rootDigest then
        [s!"stored rootDigest mismatch: expected {storedRootDigest}, got {a.rootDigest}"]
      else
        [])
    ++
      (if verifiedRootDigest != "" && a.rootDigest != verifiedRootDigest then
        [s!"artifact rootDigest mismatch: expected {verifiedRootDigest}, got {a.rootDigest}"]
      else
        [])

  let errors₆ :=
    match nodes? with
    | none => []
    | some nodes =>
        Id.run do
          let mut acc : List String := []

          if a.nodes.size != nodes.size then
            acc := acc.concat s!"stored nodes size mismatch: {a.nodes.size} != {nodes.size}"
          else
            for i in [:nodes.size] do
              match nodes[i]? , a.nodes[i]? with
              | some g, some gStored =>
                  let want := sha256HexJson mode (preGameToJson g)
                  let got := sha256HexJson mode (preGameToJson gStored)
                  if want != got then
                    acc := acc.concat s!"stored node mismatch at idx {i}"
              | _, _ =>
                  acc := acc.concat s!"stored node idx out of range: {i}"

          if a.steps.size != nodes.size then
            acc := acc.concat s!"steps size mismatch: {a.steps.size} != {nodes.size}"
          else
            let mut prev : String := ""
            for i in [:nodes.size] do
              match a.steps[i]? with
              | none =>
                  acc := acc.concat s!"step idx out of range: {i}"
              | some s =>
                  let idx : Nat := i
                  if s.idx != idx then
                    acc := acc.concat s!"step idx field mismatch at position {idx}: got {s.idx}"

                  let opWant :=
                    match a.program.getOp? idx with
                    | some op => op
                    | none => Op.unmark
                  if s.op != opWant then
                    acc := acc.concat s!"step op mismatch at idx {idx}"

                  let g? := nodes[i]?
                  match g? with
                  | none =>
                      acc := acc.concat s!"internal: nodes idx out of range: {idx}"
                  | some g =>
                      if s.birth != g.birth then
                        acc := acc.concat s!"step birth mismatch at idx {idx}"

                      let nodeDigestWant := sha256HexJson mode (preGameToJson g)
                      if s.nodeDigest != nodeDigestWant then
                        acc := acc.concat s!"nodeDigest mismatch at idx {idx}"

                      if s.prevDigest != prev then
                        acc := acc.concat s!"prevDigest mismatch at idx {idx}"

                      let core : ForwardStep := { s with stepDigest := "" }
                      let stepDigestWant := sha256HexJson mode (forwardStepCoreJson core)
                      if s.stepDigest != stepDigestWant then
                        acc := acc.concat s!"stepDigest mismatch at idx {idx}"

                      prev := s.stepDigest

            if a.finalStepDigest != prev then
              acc := acc.concat s!"finalStepDigest mismatch: expected {prev}, got {a.finalStepDigest}"

          return acc

  let errors := errors₀ ++ errors₁ ++ errors₂ ++ errors₃ ++ errors₄ ++ errors₅ ++ errors₆
  let ok := errors.isEmpty

  let baseReport : VerifyReport :=
    { ok := ok
      errors := errors
      verifiedRootDigest := verifiedRootDigest
      backwardToken := { alg := alg, digest := "" }
      tokenPair := { forward := a.forwardToken, backward := { alg := alg, digest := "" } } }

  let backwardDigest := sha256HexJson mode (Lean.toJson baseReport)
  let backwardToken : ReferenceToken := { alg := alg, digest := backwardDigest }
  let pair : BidirectionalTokenPair := { forward := a.forwardToken, backward := backwardToken }
  { ok := ok
    errors := errors
    verifiedRootDigest := verifiedRootDigest
    backwardToken := backwardToken
    tokenPair := pair }

/-! ## Dialectica wrapper (minimal) -/

structure DialecticaWitness where
  forward : ForwardArtifact
  deriving Repr

structure DialecticaChallenge where
  query : VerifyQuery
  deriving Repr

def dialecticaRespond (w : DialecticaWitness) (c : DialecticaChallenge) : VerifyReport :=
  verify w.forward c.query

/-! ## Sheaf-style gluing (minimal coherence) -/

/-- "Glue" witnesses if they agree on the forward digest. -/
def glueWitnesses (ws : List DialecticaWitness) : Except String DialecticaWitness := do
  match ws with
  | [] => throw "cannot glue empty witness family"
  | w :: rest =>
      let d := w.forward.forwardToken.digest
      for w' in rest do
        if w'.forward.forwardToken.digest != d then
          throw s!"witness digest mismatch: {w'.forward.forwardToken.digest} != {d}"
      return w

end BidirectionalProof

end Surreal
end Numbers
end HeytingLean
