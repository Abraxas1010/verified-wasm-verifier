import Lean
import Lean.Data.Json

namespace HeytingLean
namespace Payments

open Lean

structure Budget where
  id   : String
  cap  : String
  unit : String -- "day" | "week" | "month" | "fixed"
  deriving Repr, Inhabited, BEq

structure Policy where
  allowedRecipientsMode : String -- "verified" | "custom" | "all"
  customRecipients      : List String := []
  caps_perTx            : String
  caps_perDay           : String
  budgets               : List Budget := []
  verifiedRoot          : Option String := none
  deriving Repr, Inhabited

structure BudgetSpend where
  epoch? : Option Nat := none
  spent  : String
  deriving Repr, Inhabited

structure State where
  epoch        : Nat
  spentToday   : String
  txCount      : Nat
  budgetsSpent : List (String × BudgetSpend) := [] -- map: id → BudgetSpend
  deriving Repr, Inhabited

structure Request where
  hashedId      : String
  recipient     : String
  amount        : String
  budget_id     : String
  epoch         : Nat
  walletAddress : Option String := none
  verifiedOk    : Option Bool := none
  deriving Repr, Inhabited

namespace JsonCodec

open Lean (Json)

def getStr (j : Json) (k : String) : Except String String := do
  match j.getObjVal? k with
  | .ok v =>
      match v.getStr? with
      | .ok s => return s
      | .error _ => .error s!"field '{k}' not a string"
  | .error _ => .error s!"missing string field '{k}'"

def getNat (j : Json) (k : String) : Except String Nat := do
  match j.getObjVal? k with
  | .ok v =>
      match v.getNat? with
      | .ok n => return n
      | .error _ => .error s!"field '{k}' not a nat"
  | .error _ => .error s!"missing nat field '{k}'"

def getArr (j : Json) (k : String) : Except String (Array Json) := do
  match j.getObjVal? k with
  | .ok v =>
      match v.getArr? with
      | .ok a => return a
      | .error _ => .error s!"field '{k}' not an array"
  | .error _ => .error s!"missing array field '{k}'"

def optStr (j : Json) (k : String) : Option String :=
  match j.getObjVal? k with
  | .ok v => (v.getStr?).toOption
  | .error _ => none

def optNat (j : Json) (k : String) : Option Nat :=
  match j.getObjVal? k with
  | .ok v => (v.getNat?).toOption
  | .error _ => none

def parseBudget (j : Json) : Except String Budget := do
  let id ← getStr j "id"
  let cap ← getStr j "cap"
  let unit ← getStr j "unit"
  return { id, cap, unit }

def parsePolicy (j : Json) : Except String Policy := do
  let mode ← getStr j "allowedRecipientsMode"
  let capsJ ← match j.getObjVal? "caps" with | .ok jj => pure jj | .error _ => .error "missing caps"
  let perTx ← getStr capsJ "perTx"
  let perDay ← getStr capsJ "perDay"
  let recip : List String := match j.getObjVal? "customRecipients" with
    | .ok arr =>
        match arr.getArr? with
        | .ok a => a.toList.filterMap (fun x => (x.getStr?).toOption)
        | .error _ => []
    | .error _ => []
  let budgets : List Budget := match j.getObjVal? "budgets" with
    | .ok (.arr a) =>
        match (a.toList.mapM parseBudget) with
        | .ok lst => lst
        | .error _ => []
    | _ => []
  let vRoot : Option String :=
    match j.getObjVal? "verifiedRoot" with
    | .ok (.str s) => some s
    | _ => none
  return { allowedRecipientsMode := mode
         , customRecipients := recip
         , caps_perTx := perTx
         , caps_perDay := perDay
         , budgets, verifiedRoot := vRoot }

def parseBudgetSpend (j : Json) : Except String BudgetSpend := do
  let epoch? := optNat j "epoch"
  let spent ← getStr j "spent"
  return { epoch? := epoch?, spent }

def parseState (j : Json) : Except String State := do
  let epoch ← getNat j "epoch"
  let spentToday ← getStr j "spentToday"
  let txCount ← getNat j "txCount"
  -- budgetsSpent optional; prefer array form `budgetsSpentArr` [{id, epoch?, spent}]
  let bsMap : List (String × BudgetSpend) :=
    match j.getObjVal? "budgetsSpentArr" with
    | .ok (.arr a) =>
        let rec loop (xs : List Json) (acc : List (String × BudgetSpend)) : List (String × BudgetSpend) :=
          match xs with
          | [] => acc
          | x :: xt =>
              let id := match x.getObjVal? "id" with | .ok (.str s) => s | _ => ""
              let spent := match x.getObjVal? "spent" with | .ok (.str s) => s | _ => "0"
              let epoch? := match x.getObjVal? "epoch" with | .ok v => (v.getNat?).toOption | _ => none
              let bs : BudgetSpend := { epoch? := epoch?, spent := spent }
              let acc' := if id == "" then acc else (id, bs) :: acc
              loop xt acc'
        loop a.toList []
    | _ => []
  return { epoch, spentToday, txCount, budgetsSpent := bsMap }

def parseRequest (j : Json) : Except String Request := do
  let hashedId ← getStr j "hashedId"
  let recipient ← getStr j "recipient"
  let amount ← getStr j "amount"
  let budget_id ← getStr j "budget_id"
  let epoch ← getNat j "epoch"
  let walletAddress := optStr j "walletAddress"
  let verifiedOk :=
    match j.getObjVal? "verifiedOk" with
    | .ok v => (v.getBool?).toOption
    | .error _ => none
  return { hashedId, recipient, amount, budget_id, epoch, walletAddress, verifiedOk }

/- Canonical JSON encoders for stable commitment payloads. -/
def policyToCanonicalJson (p : Policy) : Json :=
  let recips := p.customRecipients
  let budgets := p.budgets
  let recipsArr := recips.map Json.str |>.toArray
  let budgetsArr := budgets.map (fun b => Json.mkObj
        [ ("id", Json.str b.id), ("cap", Json.str b.cap), ("unit", Json.str b.unit) ] ) |>.toArray
  let base := [ ("allowedRecipientsMode", Json.str p.allowedRecipientsMode)
              , ("customRecipients", Json.arr recipsArr)
              , ("caps", Json.mkObj [ ("perTx", Json.str p.caps_perTx)
                                     , ("perDay", Json.str p.caps_perDay) ])
              , ("budgets", Json.arr budgetsArr) ]
  let withRoot := match p.verifiedRoot with
    | some r => ("verifiedRoot", Json.str r) :: base
    | none => base
  Json.mkObj withRoot

def stateToCanonicalJson (s : State) : Json :=
  let bs := s.budgetsSpent
  let bsArr := bs.map (fun (k,v) =>
    let base := [("spent", Json.str v.spent)]
    let fields := match v.epoch? with | some e => ("epoch", Json.num e) :: base | none => base
    Json.mkObj (("id", Json.str k) :: fields)) |>.toArray
  Json.mkObj
    [ ("epoch", Json.num s.epoch)
    , ("spentToday", Json.str s.spentToday)
    , ("txCount", Json.num s.txCount)
    , ("budgetsSpent", Json.arr bsArr)
    ]

end JsonCodec

end Payments
end HeytingLean
