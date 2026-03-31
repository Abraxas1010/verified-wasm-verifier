import Lean
import HeytingLean.BountyHunter.Solc.YulTextMini.Types
import HeytingLean.BountyHunter.Solc.YulTextMini.Parse
import HeytingLean.BountyHunter.Solc.YulTextMini.Effects
import HeytingLean.BountyHunter.AlgebraIR.SlotRef
import Lean.Data.RBMap

/-!
# HeytingLean.BountyHunter.Solc.YulTextMini.DeltaInvariants

MVP "spec-free inconsistency" scan:

Extract storage updates of the form:
- `sstore(slot, add(sload(slot), Δ))`
- `sstore(slot, sub(sload(slot), Δ))`

and treat them as *delta updates* to storage slots. Then flag potential
conservation inconsistencies within a slot-group (e.g. mapping base).

This is intentionally heuristic and conservative: results are **candidates**
that require manual review.
-/

namespace HeytingLean.BountyHunter.Solc.YulTextMini

open Std
open Lean
open HeytingLean.BountyHunter.AlgebraIR

/-! ## Canonicalized additive expressions (very small nucleus) -/

abbrev Atom := String

structure CanonDelta where
  terms : RBMap Atom Int compare := {}
  deriving Repr, Inhabited

def CanonDelta.isZero (c : CanonDelta) : Bool :=
  c.terms.isEmpty

def CanonDelta.coeff (c : CanonDelta) (a : Atom) : Int :=
  c.terms.find? a |>.getD 0

def CanonDelta.addTerm (c : CanonDelta) (a : Atom) (k : Int) : CanonDelta :=
  if k = 0 then
    c
  else
    match c.terms.find? a with
    | none =>
        { terms := c.terms.insert a k }
    | some k0 =>
        let k1 := k0 + k
        if k1 = 0 then
          { terms := c.terms.erase a }
        else
          { terms := c.terms.insert a k1 }

def CanonDelta.add (a b : CanonDelta) : CanonDelta :=
  Lean.RBMap.fold (fun acc atom k => acc.addTerm atom k) a b.terms

def CanonDelta.scale (k : Int) (a : CanonDelta) : CanonDelta :=
  if k = 0 then
    {}
  else
    Lean.RBMap.fold (fun acc atom c => acc.addTerm atom (k * c)) {} a.terms

def CanonDelta.toJson (c : CanonDelta) : Json :=
  Json.arr <|
    Lean.RBMap.fold
      (fun acc atom k => acc.push (Json.mkObj [("atom", Json.str atom), ("coeff", Json.num (Lean.JsonNumber.fromInt k))]))
      #[]
      c.terms

partial def canonOfExpr (e : Expr) (sign : Int := 1) : CanonDelta :=
  match e with
  | .call fn args =>
      let isAddLike : Bool :=
        fn = "add" || fn.startsWith "checked_add" || fn.startsWith "wrapping_add"
      let isSubLike : Bool :=
        fn = "sub" || fn.startsWith "checked_sub" || fn.startsWith "wrapping_sub"
      if isAddLike then
        match args[0]?, args[1]? with
        | some a, some b => (canonOfExpr a sign).add (canonOfExpr b sign)
        | _, _ => ({ : CanonDelta }).addTerm (exprRender e) sign
      else if isSubLike then
        match args[0]?, args[1]? with
        | some a, some b => (canonOfExpr a sign).add (canonOfExpr b (-sign))
        | _, _ => ({ : CanonDelta }).addTerm (exprRender e) sign
      else
        ({ : CanonDelta }).addTerm (exprRender e) sign
  | .nat n =>
      if n = 0 then {} else ({ : CanonDelta }).addTerm (exprRender e) sign
  | _ =>
      ({ : CanonDelta }).addTerm (exprRender e) sign

private def CanonDelta.allCoeffs (c : CanonDelta) (p : Int → Bool) : Bool :=
  Lean.RBMap.fold (fun acc _atom k => acc && p k) true c.terms

private def CanonDelta.allNonneg (c : CanonDelta) : Bool :=
  c.allCoeffs (fun k => k ≥ 0)

private def CanonDelta.allNonpos (c : CanonDelta) : Bool :=
  c.allCoeffs (fun k => k ≤ 0)

/-! ## Slot delta extraction -/

structure SlotDelta where
  slotRef : SlotRef
  slotExpr : String
  groupKey : String
  delta : CanonDelta
  op : String
  deltaRaw : String
  deriving Repr, Inhabited

def slotGroupKey (r : SlotRef) : String :=
  match r with
  | .mapping base _ => s!"mapping_base:{slotRefToString base}"
  | .keccak base => s!"keccak:{slotRefToString base}"
  | .add base off => s!"add_base:{slotRefToString base}:{slotOffsetToString off}"
  | .packed base off bytes => s!"packed_base:{slotRefToString base}:{off}:{bytes}"
  | _ => s!"slot:{slotRefToString r}"

private def containsSubstr (hay needle : String) : Bool :=
  if needle.isEmpty then
    true
  else
    Id.run do
      let max := hay.length - needle.length
      let mut found := false
      for i in [:max.succ] do
        if (!found) && (hay.drop i).startsWith needle then
          found := true
      return found

private def isLoadLikeFn (fn : String) : Bool :=
  fn = "sload" ||
  fn.startsWith "read_from_storage_offset_" ||
  fn.startsWith "read_from_storage_split_offset_" ||
  fn.startsWith "load_from_storage_offset_"

private def isLoadAtomStr (s : String) : Bool :=
  s.startsWith "sload(" ||
  s.startsWith "read_from_storage_offset_" ||
  s.startsWith "read_from_storage_split_offset_" ||
  s.startsWith "load_from_storage_offset_"

private def slotDeltaFromSStore? (env : Env) (slotE valE : Expr) : Option SlotDelta :=
  let rec substExpr (e : Expr) (fuel : Nat := 20) : Expr :=
    if fuel = 0 then
      e
    else
      match e with
      | .ident name =>
          match env.get? name with
          | none => e
          | some e' => substExpr e' (fuel - 1)
      | .call fn args =>
          .call fn (args.map (fun a => substExpr a (fuel - 1)))
      | other => other

  let slotE := substExpr slotE 20
  let valE := substExpr valE 20
  let slot := slotRefOfExpr env slotE
  let slotRendered := exprRender slotE
  let slotExpr := slotRefToString slot
  let group := slotGroupKey slot

  let rec collectSloadAtoms (e : Expr) (acc : Array Atom) : Array Atom :=
    match e with
    | .call fn args =>
        if isLoadLikeFn fn then
          match args[0]? with
          | some a =>
              let a' := substExpr a 5
              let sameSlotRef := slotRefOfExpr env a' = slot
              let sameSlotRender := exprRender a' = slotRendered
              if sameSlotRef || sameSlotRender then
                acc.push (exprRender e)
              else
                acc
          | none => acc
        else
          args.foldl (fun a e => collectSloadAtoms e a) acc
    | _ => acc

  -- General additive-chain pattern:
  -- if `canon(valE)` contains `+1 * sload(slot)`, treat the rest as Δ.
  let sloadAtoms := collectSloadAtoms valE #[]
  let valCanon := canonOfExpr valE 1
  let sloadKeys : Array Atom :=
    Lean.RBMap.fold
      (fun acc atom _k => if isLoadAtomStr atom then acc.push atom else acc)
      #[]
      valCanon.terms
  let picked? : Option Atom :=
    if sloadKeys.size = 1 && valCanon.coeff sloadKeys[0]! = 1 then
      some sloadKeys[0]!
    else
      match sloadAtoms.find? (fun a => valCanon.coeff a = 1) with
      | some a => some a
      | none =>
          sloadKeys.find? (fun a => valCanon.coeff a = 1 && containsSubstr a slotRendered)
  match picked? with
  | some sloadAtom =>
    let deltaCanon := valCanon.addTerm sloadAtom (-1)
    let op :=
      if deltaCanon.allNonneg then
        "sstore=add"
      else if deltaCanon.allNonpos then
        "sstore=sub"
      else
        "sstore=mixed"
    some
      { slotRef := slot
        slotExpr := slotExpr
        groupKey := group
        delta := deltaCanon
        op := op
        deltaRaw := exprRender valE
      }
  | none =>
      none

private def deltasFromExpr (env : Env) (e : Expr) : Array SlotDelta :=
  match e with
  | .call "sstore" args =>
      match args[0]?, args[1]? with
      | some slotE, some valE =>
          match slotDeltaFromSStore? env slotE valE with
          | some d => #[d]
          | none => #[]
      | _, _ => #[]
  | .call fn args =>
      if fn.startsWith "update_storage_value_offset" || fn.startsWith "update_storage_value_" then
        match args[0]?, args.back? with
        | some slotE, some valE =>
            match slotDeltaFromSStore? env slotE valE with
            | some d => #[d]
            | none => #[]
        | _, _ => #[]
      else
        #[]
  | _ => #[]

mutual
  partial def collectDeltasFromStmt (env : Env) (s : Stmt) : Array SlotDelta :=
    match s with
    | .let_ _ rhs => deltasFromExpr env rhs
    | .letMany _ rhs => deltasFromExpr env rhs
    | .assign _ rhs => deltasFromExpr env rhs
    | .assignMany _ rhs => deltasFromExpr env rhs
    | .expr e => deltasFromExpr env e
    | .block ss => collectDeltasFromStmts env ss
    | .if_ cond thenStmts =>
        deltasFromExpr env cond ++ collectDeltasFromStmts env thenStmts
    | .switch_ scrut cases def? =>
        let fromCases :=
          cases.foldl (fun acc c => acc ++ collectDeltasFromStmts env c.2) #[]
        let fromDef :=
          match def? with
          | none => #[]
          | some ss => collectDeltasFromStmts env ss
        deltasFromExpr env scrut ++ fromCases ++ fromDef
    | .for_ init cond post body =>
        let initD := collectDeltasFromStmts env init
        let env2 := init.foldl (fun e st => updateEnv e st) env
        initD ++ deltasFromExpr env2 cond ++ collectDeltasFromStmts env2 post ++ collectDeltasFromStmts env2 body
    | .break => #[]
    | .continue => #[]
    | .return_ _ => #[]
    | .revert _ => #[]
    | .leave => #[]

  partial def collectDeltasFromStmts (env0 : Env) (ss : Array Stmt) : Array SlotDelta :=
    Id.run do
      let mut env := env0
      let mut out : Array SlotDelta := #[]
      for s in ss do
        out := out ++ collectDeltasFromStmt env s
        env := updateEnv env s
      pure out
end

/-! ## Heuristic inconsistency checks -/

structure InconsistencyFinding where
  groupKey : String
  netDelta : CanonDelta
  slots : Array String
  updates : Array SlotDelta
  reason : String
  deriving Repr, Inhabited

def SlotDelta.toJson (d : SlotDelta) : Json :=
  Json.mkObj
    [ ("slotExpr", Json.str d.slotExpr)
    , ("groupKey", Json.str d.groupKey)
    , ("op", Json.str d.op)
    , ("deltaRaw", Json.str d.deltaRaw)
    , ("deltaCanon", d.delta.toJson)
    ]

def InconsistencyFinding.toJson (f : InconsistencyFinding) : Json :=
  Json.mkObj
    [ ("groupKey", Json.str f.groupKey)
    , ("reason", Json.str f.reason)
    , ("netDelta", f.netDelta.toJson)
    , ("slots", Json.arr (f.slots.map Json.str))
    , ("updates", Json.arr (f.updates.map SlotDelta.toJson))
    ]

private def uniqStrings (xs : Array String) : Array String :=
  Id.run do
    let ys := xs.qsort (fun a b => a < b)
    let mut out : Array String := #[]
    for x in ys do
      match out.back? with
      | none => out := out.push x
      | some y => if x = y then continue else out := out.push x
    return out

def scanDeltaInconsistencies (ds : Array SlotDelta) : Array InconsistencyFinding :=
  Id.run do
    let mut groups : HashMap String (Array SlotDelta) := HashMap.emptyWithCapacity (ds.size + 1)
    for d in ds do
      let cur := groups.getD d.groupKey #[]
      groups := groups.insert d.groupKey (cur.push d)

    let mut out : Array InconsistencyFinding := #[]
    for (gk, arr) in groups.toList do
      if arr.size < 2 then
        continue
      let slots := uniqStrings (arr.map (·.slotExpr))
      if slots.size < 2 then
        continue
      let hasPos := arr.any (fun d => d.op.startsWith "sstore=add")
      let hasNeg := arr.any (fun d => d.op.startsWith "sstore=sub")
      if !(hasPos && hasNeg) then
        continue
      let net := arr.foldl (fun acc d => acc.add d.delta) ({ : CanonDelta })
      if net.isZero then
        continue
      out := out.push
        { groupKey := gk
          netDelta := net
          slots := slots
          updates := arr
          reason := "heuristic: mapping-like slot group has both +Δ and -Δ updates but net delta ≠ 0"
        }
    return out

def scanIRInconsistencies (ir : String) (fn : String) : Except String (Array InconsistencyFinding × Array SlotDelta) := do
  let body ← HeytingLean.BountyHunter.Solc.YulTextMini.parseFunctionBodyE ir fn
  let ds := collectDeltasFromStmts envEmpty body
  let fs := scanDeltaInconsistencies ds
  return (fs, ds)

end HeytingLean.BountyHunter.Solc.YulTextMini
