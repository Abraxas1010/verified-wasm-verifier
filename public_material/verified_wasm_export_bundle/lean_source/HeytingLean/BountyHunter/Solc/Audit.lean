import Lean
import Std
import Lean.Data.Json
import HeytingLean.Util.JCS
import HeytingLean.BountyHunter.Solc.ExtractIR
import HeytingLean.BountyHunter.Solc.YulTextMini
import HeytingLean.BountyHunter.Solc.YulTextMini.Parse
import HeytingLean.BountyHunter.Solc.YulTextMini.Pretty
import HeytingLean.BountyHunter.Solc.YulTextMini.Risk
import HeytingLean.BountyHunter.AlgebraIR.Types
import HeytingLean.BountyHunter.AlgebraIR.Json
import HeytingLean.BountyHunter.AlgebraIR.CEI
import HeytingLean.BountyHunter.AlgebraIR.BackYulTextMini

/-!
# HeytingLean.BountyHunter.Solc.Audit

Deterministic “translation audit” artifact for the current one-way pipeline:

`solc ir/irOptimized string` → `YulTextMini tokens/AST` → `AlgebraIR CFG` → `checkCEI`.

This is a debugging / verification spine: it makes each stage inspectable in JSON
so humans (and downstream tools) can validate that the intended effects are being
preserved by the translation.
-/

namespace HeytingLean.BountyHunter.Solc

open Lean
open Lean.Json
open HeytingLean.BountyHunter

namespace Audit

structure MissingEffect where
  kind : String
  slot? : Option Nat := none
  target? : Option String := none
  deriving Repr, DecidableEq, Inhabited

structure TranslationChecks where
  expectedEffects : Array AlgebraIR.Effect := #[]
  observedEffects : Array AlgebraIR.Effect := #[]
  missingEffects : Array MissingEffect := #[]
  ok : Bool := true
  deriving Repr, DecidableEq, Inhabited

structure Artifact where
  version : String := "solc.translation_audit.v0"
  sourceUnit : String
  contractName : String
  field : String
  desiredFunc : String
  selectedFunc : String
  slot : Nat
  slotExpr? : Option String := none
  irLen : Nat
  irFnv1a64 : String
  bodyTokCount : Nat
  bodyTokens : Json
  bodyTokensRendered : Json
  bodyAst : Json
  bodyPretty : String := ""
  bodyPrettyIdempotent : Bool := false
  algebrair : Json
  algebrairBackYul? : Option String := none
  algebrairBackYulIdempotent : Bool := false
  algebrairBackYulError? : Option String := none
  witnessBackYul? : Option String := none
  witnessBackYulIdempotent : Bool := false
  witnessBackYulError? : Option String := none
  verdict : String
  witness? : Option Json := none
  translationChecks : TranslationChecks := {}
  risk : YulTextMini.RiskReport := {}

private def fnv1a64Hex (s : String) : String :=
  let bytes := s.toUTF8
  let offset : UInt64 := 14695981039346656037
  let prime : UInt64 := 1099511628211
  let h : UInt64 :=
    Id.run do
      let mut h := offset
      for b in bytes do
        h := (h.xor (UInt64.ofNat b.toNat)) * prime
      return h
  -- `toString` is deterministic, even if not hex. Prefix to make it obvious.
  s!"u64:{toString h}"

private def effectKey (e : AlgebraIR.Effect) : String :=
  match e with
  | .storageRead slot => s!"storageRead:{slot}"
  | .storageReadDyn slotExpr => s!"storageReadDyn:{slotExpr}"
  | .storageWrite slot => s!"storageWrite:{slot}"
  | .storageWriteDyn slotExpr => s!"storageWriteDyn:{slotExpr}"
  | .boundaryCall t => s!"boundaryCall:{t}"

private def missingOfKey (k : String) : MissingEffect :=
  if k.startsWith "storageRead:" then
    { kind := "storageRead", slot? := (k.drop "storageRead:".length).toNat? }
  else if k.startsWith "storageReadDyn:" then
    { kind := "storageReadDyn", target? := some (k.drop "storageReadDyn:".length) }
  else if k.startsWith "storageWrite:" then
    { kind := "storageWrite", slot? := (k.drop "storageWrite:".length).toNat? }
  else if k.startsWith "storageWriteDyn:" then
    { kind := "storageWriteDyn", target? := some (k.drop "storageWriteDyn:".length) }
  else if k.startsWith "boundaryCall:" then
    { kind := "boundaryCall", target? := some (k.drop "boundaryCall:".length) }
  else
    { kind := k }

private def flatEffectsOfGraph (g : AlgebraIR.Graph) : Array AlgebraIR.Effect :=
  g.nodes.foldl (fun acc n => acc ++ n.effects) #[]

private def checkEffectsCovered (expected observed : Array AlgebraIR.Effect) : TranslationChecks :=
  Id.run do
    let mut obs := Std.HashSet.emptyWithCapacity (observed.size + 1)
    for e in observed do
      obs := obs.insert (effectKey e)
    let mut missing : Array MissingEffect := #[]
    for e in expected do
      let k := effectKey e
      if !obs.contains k then
        missing := missing.push (missingOfKey k)
    pure
      { expectedEffects := expected
        observedEffects := observed
        missingEffects := missing
        ok := missing.isEmpty
      }

def translationChecksToJson (c : TranslationChecks) : Json :=
  Json.mkObj
    [ ("ok", Json.bool c.ok)
    , ("expectedEffects", Json.arr (c.expectedEffects.map AlgebraIR.effectToJson))
    , ("observedEffects", Json.arr (c.observedEffects.map AlgebraIR.effectToJson))
    , ("missingEffects",
        Json.arr <|
          c.missingEffects.map (fun m =>
            let base := [("kind", Json.str m.kind)]
            let base :=
              match m.slot? with
              | none => base
              | some n => base ++ [("slot", Json.num n)]
            let base :=
              match m.target? with
              | none => base
              | some s => base ++ [("target", Json.str s)]
            Json.mkObj base))
    ]

def artifactToJson (a : Artifact) : Json :=
  let base :=
    [ ("version", Json.str a.version)
    , ("sourceUnit", Json.str a.sourceUnit)
    , ("contractName", Json.str a.contractName)
    , ("field", Json.str a.field)
    , ("desiredFunc", Json.str a.desiredFunc)
    , ("selectedFunc", Json.str a.selectedFunc)
    , ("slot", Json.num a.slot)
    , ("irLen", Json.num a.irLen)
    , ("irFnv1a64", Json.str a.irFnv1a64)
    , ("bodyTokCount", Json.num a.bodyTokCount)
    , ("bodyTokens", a.bodyTokens)
    , ("bodyTokensRendered", a.bodyTokensRendered)
    , ("bodyAst", a.bodyAst)
    , ("bodyPretty", Json.str a.bodyPretty)
    , ("bodyPrettyIdempotent", Json.bool a.bodyPrettyIdempotent)
    , ("algebrair", a.algebrair)
    , ("algebrairBackYulIdempotent", Json.bool a.algebrairBackYulIdempotent)
    , ("verdict", Json.str a.verdict)
    , ("translationChecks", translationChecksToJson a.translationChecks)
    , ("risk", YulTextMini.riskToJson (YulTextMini.normalize a.risk))
    ]
  let base :=
    match a.algebrairBackYul? with
    | none => base
    | some s => base ++ [("algebrairBackYul", Json.str s)]
  let base :=
    match a.algebrairBackYulError? with
    | none => base
    | some s => base ++ [("algebrairBackYulError", Json.str s)]
  let base :=
    match a.witnessBackYul? with
    | none => base
    | some s => base ++ [("witnessBackYul", Json.str s)]
  let base := base ++ [("witnessBackYulIdempotent", Json.bool a.witnessBackYulIdempotent)]
  let base :=
    match a.witnessBackYulError? with
    | none => base
    | some s => base ++ [("witnessBackYulError", Json.str s)]
  let base :=
    match a.slotExpr? with
    | none => base
    | some s => base ++ [("slotExpr", Json.str s)]
  let base :=
    match a.witness? with
    | none => base
    | some w => base ++ [("witness", w)]
  Json.mkObj base

def artifactCanonicalString (a : Artifact) : String :=
  HeytingLean.Util.JCS.canonicalString (artifactToJson a)

def mkFromIR (sel : Selector) (ir : String) (desiredFunc : String) (selectedFunc : String)
    (slot : Nat) (slotExpr? : Option String := none) : Except String Artifact := do
  let bodyToks ← YulTextMini.findFunctionBodyTokensE ir selectedFunc
  let body ← YulTextMini.parseFunctionBodyE ir selectedFunc
  let g := YulTextMini.toAlgebraIR body
  let (v, w?) :=
    match slotExpr? with
    | none => AlgebraIR.checkCEI g slot
    | some se => AlgebraIR.checkCEISlotExpr g se
  let verdictStr :=
    match v with
    | .safe => "SAFE"
    | .vulnerable => "VULNERABLE"
    | .outOfScope r => s!"OUT_OF_SCOPE:{r}"
  let witnessJ? := w?.map AlgebraIR.ceiWitnessToJson
  let expected := YulTextMini.expectedEffectsFromStmts YulTextMini.envEmpty body
  let observed := flatEffectsOfGraph g
  let checks := checkEffectsCovered expected observed
  let bodyPretty := YulTextMini.stmtsToCanonicalString body
  let bodyPrettyIdempotent :=
    match YulTextMini.parseStmtsFromStringE bodyPretty with
    | .error _ => false
    | .ok ss => YulTextMini.stmtsToCanonicalString ss = bodyPretty
  let (backYul?, backYulIdempotent, backYulErr?) :=
    match HeytingLean.BountyHunter.AlgebraIR.BackYulTextMini.programToStringE g with
    | .error e => (none, false, some e)
    | .ok s =>
        let ok :=
          match YulTextMini.parseStmtsFromStringE s with
          | .error _ => false
          | .ok ss => YulTextMini.stmtsToCanonicalString ss = s
        (some s, ok, none)
  let (wBack?, wBackIdempotent, wBackErr?) :=
    match w? with
    | none => (none, false, none)
    | some w =>
        match HeytingLean.BountyHunter.AlgebraIR.BackYulTextMini.programToStringFromPathE g w.path with
        | .error e => (none, false, some e)
        | .ok s =>
            let ok :=
              match YulTextMini.parseStmtsFromStringE s with
              | .error _ => false
              | .ok ss => YulTextMini.stmtsToCanonicalString ss = s
            (some s, ok, none)
  pure
    { sourceUnit := sel.sourceUnit
      contractName := sel.contractName
      field := sel.field
      desiredFunc := desiredFunc
      selectedFunc := selectedFunc
      slot := slot
      slotExpr? := slotExpr?
      irLen := ir.length
      irFnv1a64 := fnv1a64Hex ir
      bodyTokCount := bodyToks.size
      bodyTokens := YulTextMini.toksToJson bodyToks
      bodyTokensRendered := YulTextMini.toksRenderedToJson bodyToks
      bodyAst := YulTextMini.stmtsToJson body
      bodyPretty := bodyPretty
      bodyPrettyIdempotent := bodyPrettyIdempotent
      algebrair := AlgebraIR.graphToJson g
      algebrairBackYul? := backYul?
      algebrairBackYulIdempotent := backYulIdempotent
      algebrairBackYulError? := backYulErr?
      witnessBackYul? := wBack?
      witnessBackYulIdempotent := wBackIdempotent
      witnessBackYulError? := wBackErr?
      verdict := verdictStr
      witness? := witnessJ?
      translationChecks := checks
      risk := YulTextMini.scanStmts body
    }

end Audit
end HeytingLean.BountyHunter.Solc
