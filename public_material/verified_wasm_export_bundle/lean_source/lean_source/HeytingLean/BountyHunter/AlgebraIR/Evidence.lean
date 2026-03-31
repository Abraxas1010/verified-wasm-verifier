import Lean
import Std
import Lean.Data.Json
import HeytingLean.Util.JCS
import HeytingLean.BountyHunter.AlgebraIR.Types

/-!
# HeytingLean.BountyHunter.AlgebraIR.Evidence

Minimal, executable-first “lattice of evidence” spine for AlgebraIR.

This module defines:
- an `Evidence` record (facts discovered about a given AlgebraIR instance),
- deterministic normalization/merge (so evidence is stable across runs),
- deterministic JSON I/O (for toolchain integration).

The closure operator `R` (“nucleus-style closure”) lives in `EvidenceClosure.lean`
to keep this file purely structural.
-/

namespace HeytingLean.BountyHunter.AlgebraIR
namespace Evidence

open Lean
open Lean.Json

/-! ## Fact types -/

inductive OrderKind where
  | happensBefore
  | dominates
  deriving Repr, DecidableEq, Inhabited

structure OrderFact where
  kind : OrderKind
  a : NodeId
  b : NodeId
  deriving Repr, DecidableEq, Inhabited

structure EffectFact where
  node : NodeId
  eff : Effect
  deriving Repr, DecidableEq, Inhabited

structure EqFact where
  lhs : String
  rhs : String
  deriving Repr, DecidableEq, Inhabited

structure AssumptionFact where
  prop : String
  deriving Repr, DecidableEq, Inhabited

inductive ClaimFact where
  | ceiSafe (slot : Nat)
  | ceiSafeSlotExpr (slotExpr : String)
  deriving Repr, DecidableEq, Inhabited

structure CEIPathWitness where
  boundaryNode : NodeId
  slot : Nat
  slotExpr? : Option String := none
  path : Array NodeId := #[]
  reason : String
  deriving Repr, DecidableEq, Inhabited

inductive WitnessFact where
  | ceiPath (w : CEIPathWitness)
  deriving Repr, DecidableEq, Inhabited

/-! ## Evidence carrier -/

structure Evidence where
  version : String := "algebrair.evidence.v0"
  eqs : Array EqFact := #[]
  orders : Array OrderFact := #[]
  effects : Array EffectFact := #[]
  assumptions : Array AssumptionFact := #[]
  claims : Array ClaimFact := #[]
  witnesses : Array WitnessFact := #[]
  notes : Array String := #[]
  deriving Repr, DecidableEq, Inhabited

abbrev Delta := Evidence

def empty : Evidence := {}

/-! ## Deterministic normalization -/

private def cmpThen (a b : Ordering) : Ordering :=
  match a with
  | .eq => b
  | _ => a

private def cmpArrayNat (xs ys : Array Nat) : Ordering :=
  Id.run do
    let mut i : Nat := 0
    let n := min xs.size ys.size
    while i < n do
      let c := compare xs[i]! ys[i]!
      if c ≠ .eq then
        return c
      i := i + 1
    return compare xs.size ys.size

instance : Ord OrderKind where
  compare
    | .happensBefore, .happensBefore => .eq
    | .happensBefore, _ => .lt
    | _, .happensBefore => .gt
    | .dominates, .dominates => .eq

instance : Ord Effect where
  compare
    | .storageRead a, .storageRead b => compare a b
    | .storageRead _, _ => .lt
    | _, .storageRead _ => .gt
    | .storageReadDyn a, .storageReadDyn b => compare a b
    | .storageReadDyn _, _ => .lt
    | _, .storageReadDyn _ => .gt
    | .storageWrite a, .storageWrite b => compare a b
    | .storageWrite _, _ => .lt
    | _, .storageWrite _ => .gt
    | .storageWriteDyn a, .storageWriteDyn b => compare a b
    | .storageWriteDyn _, _ => .lt
    | _, .storageWriteDyn _ => .gt
    | .boundaryCall a, .boundaryCall b => compare a b

instance : Ord OrderFact where
  compare x y :=
    cmpThen (compare x.kind y.kind) <|
    cmpThen (compare x.a y.a) (compare x.b y.b)

instance : Ord EffectFact where
  compare x y :=
    cmpThen (compare x.node y.node) (compare x.eff y.eff)

instance : Ord EqFact where
  compare x y :=
    cmpThen (compare x.lhs y.lhs) (compare x.rhs y.rhs)

instance : Ord AssumptionFact where
  compare x y := compare x.prop y.prop

instance : Ord ClaimFact where
  compare
    | .ceiSafe a, .ceiSafe b => compare a b
    | .ceiSafe _, _ => .lt
    | _, .ceiSafe _ => .gt
    | .ceiSafeSlotExpr a, .ceiSafeSlotExpr b => compare a b

instance : Ord CEIPathWitness where
  compare x y :=
    cmpThen (compare x.boundaryNode y.boundaryNode) <|
    cmpThen (compare x.slot y.slot) <|
    cmpThen (compare x.slotExpr? y.slotExpr?) <|
    cmpThen (cmpArrayNat x.path y.path) (compare x.reason y.reason)

instance : Ord WitnessFact where
  compare
    | .ceiPath a, .ceiPath b => compare a b

private def sortDedup {α : Type} [Ord α] [DecidableEq α] (xs : Array α) : Array α :=
  Id.run do
    let ys := xs.qsort (fun a b => compare a b = .lt)
    let mut out : Array α := #[]
    for x in ys do
      match out.back? with
      | none => out := out.push x
      | some y =>
          if x = y then
            continue
          else
            out := out.push x
    return out

def normalize (e : Evidence) : Evidence :=
  { e with
    eqs := sortDedup e.eqs
    orders := sortDedup e.orders
    effects := sortDedup e.effects
    assumptions := sortDedup e.assumptions
    claims := sortDedup e.claims
    witnesses := sortDedup e.witnesses
    notes := sortDedup e.notes
  }

def merge (a b : Evidence) : Evidence :=
  normalize
    { a with
      eqs := a.eqs ++ b.eqs
      orders := a.orders ++ b.orders
      effects := a.effects ++ b.effects
      assumptions := a.assumptions ++ b.assumptions
      claims := a.claims ++ b.claims
      witnesses := a.witnesses ++ b.witnesses
      notes := a.notes ++ b.notes
    }

def mergeMany (xs : Array Evidence) : Evidence :=
  xs.foldl merge empty

/-! ## JSON I/O (deterministic, canonical) -/

def orderKindToString (k : OrderKind) : String :=
  match k with
  | .happensBefore => "happensBefore"
  | .dominates => "dominates"

def orderKindFromString (s : String) : Option OrderKind :=
  match s with
  | "happensBefore" => some .happensBefore
  | "dominates" => some .dominates
  | _ => none

def effectToJson (e : Effect) : Json :=
  match e with
  | .storageRead slot =>
      Json.mkObj [("kind", Json.str "storageRead"), ("slot", Json.num (slot : Nat))]
  | .storageReadDyn slotExpr =>
      Json.mkObj [("kind", Json.str "storageReadDyn"), ("slotExpr", Json.str slotExpr)]
  | .storageWrite slot =>
      Json.mkObj [("kind", Json.str "storageWrite"), ("slot", Json.num (slot : Nat))]
  | .storageWriteDyn slotExpr =>
      Json.mkObj [("kind", Json.str "storageWriteDyn"), ("slotExpr", Json.str slotExpr)]
  | .boundaryCall target =>
      Json.mkObj [("kind", Json.str "boundaryCall"), ("target", Json.str target)]

def orderFactToJson (o : OrderFact) : Json :=
  Json.mkObj
    [ ("kind", Json.str (orderKindToString o.kind))
    , ("a", Json.num o.a)
    , ("b", Json.num o.b)
    ]

def effectFactToJson (e : EffectFact) : Json :=
  Json.mkObj [("node", Json.num e.node), ("effect", effectToJson e.eff)]

def eqFactToJson (e : EqFact) : Json :=
  Json.mkObj [("lhs", Json.str e.lhs), ("rhs", Json.str e.rhs)]

def assumptionFactToJson (a : AssumptionFact) : Json :=
  Json.mkObj [("prop", Json.str a.prop)]

def claimFactToJson (c : ClaimFact) : Json :=
  match c with
  | .ceiSafe slot =>
      Json.mkObj [("kind", Json.str "ceiSafe"), ("slot", Json.num (slot : Nat))]
  | .ceiSafeSlotExpr slotExpr =>
      Json.mkObj [("kind", Json.str "ceiSafeSlotExpr"), ("slotExpr", Json.str slotExpr)]

def ceiPathWitnessToJson (w : CEIPathWitness) : Json :=
  let base :=
    [ ("boundaryNode", Json.num w.boundaryNode)
    , ("slot", Json.num w.slot)
    , ("path", Json.arr (w.path.map (fun (x : Nat) => Json.num x)))
    , ("reason", Json.str w.reason)
    ]
  let base :=
    match w.slotExpr? with
    | none => base
    | some s => base ++ [("slotExpr", Json.str s)]
  Json.mkObj base

def witnessFactToJson (w : WitnessFact) : Json :=
  match w with
  | .ceiPath w =>
      Json.mkObj [("kind", Json.str "ceiPath"), ("w", ceiPathWitnessToJson w)]

def evidenceToJson (e : Evidence) : Json :=
  let e := normalize e
  Json.mkObj
    [ ("version", Json.str e.version)
    , ("eqs", Json.arr (e.eqs.map eqFactToJson))
    , ("orders", Json.arr (e.orders.map orderFactToJson))
    , ("effects", Json.arr (e.effects.map effectFactToJson))
    , ("assumptions", Json.arr (e.assumptions.map assumptionFactToJson))
    , ("claims", Json.arr (e.claims.map claimFactToJson))
    , ("witnesses", Json.arr (e.witnesses.map witnessFactToJson))
    , ("notes", Json.arr (e.notes.map Json.str))
    ]

def evidenceToCanonicalString (e : Evidence) : String :=
  HeytingLean.Util.JCS.canonicalString (evidenceToJson e)

namespace Internal

private def orErr {α} : Option α → String → Except String α
  | some a, _ => .ok a
  | none, msg => .error msg

def getObjE (j : Json) (ctx : String) : Except String (Std.TreeMap.Raw String Json compare) := do
  match j.getObj? with
  | .ok o => pure o
  | .error _ => .error s!"expected object ({ctx})"

def getArrE (j : Json) (ctx : String) : Except String (Array Json) := do
  match j.getArr? with
  | .ok a => pure a
  | .error _ => .error s!"expected array ({ctx})"

def getStrE (j : Json) (ctx : String) : Except String String := do
  match j.getStr? with
  | .ok s => pure s
  | .error _ => .error s!"expected string ({ctx})"

def getNatE (j : Json) (ctx : String) : Except String Nat := do
  match j.getNat? with
  | .ok n => pure n
  | .error _ => .error s!"expected Nat ({ctx})"

def getObjValE (obj : Std.TreeMap.Raw String Json compare) (k : String) (ctx : String) :
    Except String Json := do
  orErr (obj.get? k) s!"missing field '{k}' ({ctx})"

def getObjValOpt (obj : Std.TreeMap.Raw String Json compare) (k : String) : Option Json :=
  obj.get? k

end Internal

private def effectFromJsonE (j : Json) : Except String Effect := do
  let obj ← Internal.getObjE j "Effect"
  let kindJ ← Internal.getObjValE obj "kind" "Effect"
  let kind ← Internal.getStrE kindJ "Effect.kind"
  match kind with
  | "storageRead" =>
      let slotJ ← Internal.getObjValE obj "slot" "Effect.storageRead"
      pure (.storageRead (← Internal.getNatE slotJ "Effect.storageRead.slot"))
  | "storageReadDyn" =>
      let slotJ ← Internal.getObjValE obj "slotExpr" "Effect.storageReadDyn"
      pure (.storageReadDyn (← Internal.getStrE slotJ "Effect.storageReadDyn.slotExpr"))
  | "storageWrite" =>
      let slotJ ← Internal.getObjValE obj "slot" "Effect.storageWrite"
      pure (.storageWrite (← Internal.getNatE slotJ "Effect.storageWrite.slot"))
  | "storageWriteDyn" =>
      let slotJ ← Internal.getObjValE obj "slotExpr" "Effect.storageWriteDyn"
      pure (.storageWriteDyn (← Internal.getStrE slotJ "Effect.storageWriteDyn.slotExpr"))
  | "boundaryCall" =>
      let tJ ← Internal.getObjValE obj "target" "Effect.boundaryCall"
      pure (.boundaryCall (← Internal.getStrE tJ "Effect.boundaryCall.target"))
  | _ => .error s!"unknown Effect.kind '{kind}'"

private def orderFactFromJsonE (j : Json) : Except String OrderFact := do
  let obj ← Internal.getObjE j "OrderFact"
  let kindJ ← Internal.getObjValE obj "kind" "OrderFact"
  let kindS ← Internal.getStrE kindJ "OrderFact.kind"
  let kind ←
    match orderKindFromString kindS with
    | some k => pure k
    | none => throw s!"unknown OrderFact.kind '{kindS}'"
  let aJ ← Internal.getObjValE obj "a" "OrderFact"
  let bJ ← Internal.getObjValE obj "b" "OrderFact"
  pure { kind := kind, a := (← Internal.getNatE aJ "OrderFact.a"), b := (← Internal.getNatE bJ "OrderFact.b") }

private def effectFactFromJsonE (j : Json) : Except String EffectFact := do
  let obj ← Internal.getObjE j "EffectFact"
  let nodeJ ← Internal.getObjValE obj "node" "EffectFact"
  let effJ ← Internal.getObjValE obj "effect" "EffectFact"
  pure { node := (← Internal.getNatE nodeJ "EffectFact.node"), eff := (← effectFromJsonE effJ) }

private def eqFactFromJsonE (j : Json) : Except String EqFact := do
  let obj ← Internal.getObjE j "EqFact"
  let lhsJ ← Internal.getObjValE obj "lhs" "EqFact"
  let rhsJ ← Internal.getObjValE obj "rhs" "EqFact"
  pure { lhs := (← Internal.getStrE lhsJ "EqFact.lhs"), rhs := (← Internal.getStrE rhsJ "EqFact.rhs") }

private def assumptionFactFromJsonE (j : Json) : Except String AssumptionFact := do
  let obj ← Internal.getObjE j "AssumptionFact"
  let propJ ← Internal.getObjValE obj "prop" "AssumptionFact"
  pure { prop := (← Internal.getStrE propJ "AssumptionFact.prop") }

private def claimFactFromJsonE (j : Json) : Except String ClaimFact := do
  let obj ← Internal.getObjE j "ClaimFact"
  let kindJ ← Internal.getObjValE obj "kind" "ClaimFact"
  let kind ← Internal.getStrE kindJ "ClaimFact.kind"
  match kind with
  | "ceiSafe" =>
      let slotJ ← Internal.getObjValE obj "slot" "ClaimFact.ceiSafe"
      pure (.ceiSafe (← Internal.getNatE slotJ "ClaimFact.ceiSafe.slot"))
  | "ceiSafeSlotExpr" =>
      let slotJ ← Internal.getObjValE obj "slotExpr" "ClaimFact.ceiSafeSlotExpr"
      pure (.ceiSafeSlotExpr (← Internal.getStrE slotJ "ClaimFact.ceiSafeSlotExpr.slotExpr"))
  | _ => .error s!"unknown ClaimFact.kind '{kind}'"

private def ceiPathWitnessFromJsonE (j : Json) : Except String CEIPathWitness := do
  let obj ← Internal.getObjE j "CEIPathWitness"
  let bJ ← Internal.getObjValE obj "boundaryNode" "CEIPathWitness"
  let slotJ ← Internal.getObjValE obj "slot" "CEIPathWitness"
  let pathArr : Array Nat ←
    match Internal.getObjValOpt obj "path" with
    | none => pure #[]
    | some pJ =>
        let a ← Internal.getArrE pJ "CEIPathWitness.path"
        let rec go (xs : List Json) (acc : Array Nat) : Except String (Array Nat) := do
          match xs with
          | [] => pure acc
          | j :: js => go js (acc.push (← Internal.getNatE j "CEIPathWitness.path[i]"))
        go a.toList #[]
  let reasonJ ← Internal.getObjValE obj "reason" "CEIPathWitness"
  let slotExpr? : Option String :=
    match Internal.getObjValOpt obj "slotExpr" with
    | none => none
    | some j =>
        match j.getStr? with
        | .ok s => some s
        | .error _ => none
  pure
    { boundaryNode := (← Internal.getNatE bJ "CEIPathWitness.boundaryNode")
      slot := (← Internal.getNatE slotJ "CEIPathWitness.slot")
      slotExpr? := slotExpr?
      path := pathArr
      reason := (← Internal.getStrE reasonJ "CEIPathWitness.reason")
    }

private def witnessFactFromJsonE (j : Json) : Except String WitnessFact := do
  let obj ← Internal.getObjE j "WitnessFact"
  let kindJ ← Internal.getObjValE obj "kind" "WitnessFact"
  let kind ← Internal.getStrE kindJ "WitnessFact.kind"
  match kind with
  | "ceiPath" =>
      let wJ ← Internal.getObjValE obj "w" "WitnessFact.ceiPath"
      pure (.ceiPath (← ceiPathWitnessFromJsonE wJ))
  | _ => .error s!"unknown WitnessFact.kind '{kind}'"

def evidenceFromJsonE (j : Json) : Except String Evidence := do
  let obj ← Internal.getObjE j "Evidence"
  let version :=
    match Internal.getObjValOpt obj "version" with
    | some vJ =>
        match vJ.getStr? with
        | .ok s => s
        | .error _ => "algebrair.evidence.v0"
    | none => "algebrair.evidence.v0"
  let parseArr {α} (field : String) (parse : Json → Except String α) : Except String (Array α) := do
    match Internal.getObjValOpt obj field with
    | none => pure #[]
    | some aJ =>
        let a ← Internal.getArrE aJ s!"Evidence.{field}"
        let rec goParseArr (xs : List Json) (acc : Array α) : Except String (Array α) := do
          match xs with
          | [] => pure acc
          | j :: js => goParseArr js (acc.push (← parse j))
        goParseArr a.toList #[]
  let eqs ← parseArr "eqs" eqFactFromJsonE
  let orders ← parseArr "orders" orderFactFromJsonE
  let effects ← parseArr "effects" effectFactFromJsonE
  let assumptions ← parseArr "assumptions" assumptionFactFromJsonE
  let claims ← parseArr "claims" claimFactFromJsonE
  let witnesses ← parseArr "witnesses" witnessFactFromJsonE
  let notes : Array String ←
    match Internal.getObjValOpt obj "notes" with
    | none => pure #[]
    | some nJ =>
        let a ← Internal.getArrE nJ "Evidence.notes"
        let rec goNotes (xs : List Json) (acc : Array String) : Except String (Array String) := do
          match xs with
          | [] => pure acc
          | j :: js => goNotes js (acc.push (← Internal.getStrE j "Evidence.notes[i]"))
        goNotes a.toList #[]
  pure (normalize { version := version, eqs := eqs, orders := orders, effects := effects
                  , assumptions := assumptions, claims := claims, witnesses := witnesses, notes := notes })

def parseEvidenceStringE (s : String) : Except String Evidence := do
  match Lean.Json.parse s with
  | .ok j => evidenceFromJsonE j
  | .error e => .error s!"JSON parse error: {e}"

/-! ## Roundtrip helpers -/

def evidenceRoundtripPrintParseOk (e : Evidence) : Bool :=
  match parseEvidenceStringE (evidenceToCanonicalString e) with
  | .ok e' => e' = normalize e
  | .error _ => false

def evidenceRoundtripParsePrintParseE (raw : String) : Except String (String × Bool) := do
  let e ← parseEvidenceStringE raw
  let canon := evidenceToCanonicalString e
  let e2 ← parseEvidenceStringE canon
  pure (canon, e2 = normalize e)

end Evidence
end HeytingLean.BountyHunter.AlgebraIR
