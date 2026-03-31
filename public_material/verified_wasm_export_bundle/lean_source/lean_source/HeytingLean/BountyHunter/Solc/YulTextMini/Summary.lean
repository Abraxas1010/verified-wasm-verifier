import Std
import Lean.Data.Json
import HeytingLean.BountyHunter.Solc.YulTextMini.Types
import HeytingLean.BountyHunter.Solc.YulTextMini.Parse
import HeytingLean.BountyHunter.Solc.YulTextMini.Effects
import HeytingLean.BountyHunter.AlgebraIR.SlotRef

/-!
# HeytingLean.BountyHunter.Solc.YulTextMini.Summary

Phase 4 (WP2) building block: a deterministic, lightweight **summary domain** over YulTextMini
function bodies plus a small fixpoint engine (transitive closure over internal calls).

This is intentionally not a full abstract interpreter yet; it provides:
- read/write slot refs (literal + parseable dynamic),
- boundary call kinds (`call|delegatecall|callcode|staticcall`),
- internal callee names (`fun_*`, `external_fun_*`, `modifier_*`, `getter_fun_*`).

The closure is computed by joining summaries across the call graph until stable (bounded
iterations with deterministic ordering).
-/

namespace HeytingLean.BountyHunter.Solc.YulTextMini

open Std
open Lean
open HeytingLean.BountyHunter.AlgebraIR

structure FnSummary where
  version : String := "bh.yultextmini.fn_summary.v0"
  reads : Std.HashSet String := {}
  writes : Std.HashSet String := {}
  boundaryCalls : Std.HashSet String := {}
  callees : Std.HashSet String := {}
  deriving Inhabited

private def hsInsertAll (s : Std.HashSet String) (xs : Array String) : Std.HashSet String :=
  xs.foldl (fun acc x => acc.insert x) s

private def hsToSortedArray (s : Std.HashSet String) : Array String :=
  let xs := s.toList.mergeSort (fun a b => a < b)
  xs.toArray

def FnSummary.join (a b : FnSummary) : FnSummary :=
  { a with
    reads := hsInsertAll a.reads (hsToSortedArray b.reads)
    writes := hsInsertAll a.writes (hsToSortedArray b.writes)
    boundaryCalls := hsInsertAll a.boundaryCalls (hsToSortedArray b.boundaryCalls)
    callees := hsInsertAll a.callees (hsToSortedArray b.callees)
  }

def FnSummary.eqv (a b : FnSummary) : Bool :=
  (hsToSortedArray a.reads = hsToSortedArray b.reads) &&
  (hsToSortedArray a.writes = hsToSortedArray b.writes) &&
  (hsToSortedArray a.boundaryCalls = hsToSortedArray b.boundaryCalls) &&
  (hsToSortedArray a.callees = hsToSortedArray b.callees)

def FnSummary.toJson (s : FnSummary) : Json :=
  Json.mkObj
    [ ("version", Json.str s.version)
    , ("reads", Json.arr (hsToSortedArray s.reads |>.map Json.str))
    , ("writes", Json.arr (hsToSortedArray s.writes |>.map Json.str))
    , ("boundaryCalls", Json.arr (hsToSortedArray s.boundaryCalls |>.map Json.str))
    , ("callees", Json.arr (hsToSortedArray s.callees |>.map Json.str))
    ]

private def isInterestingInlineFnName (fn : String) : Bool :=
  fn.startsWith "fun_" || fn.startsWith "external_fun_" || fn.startsWith "getter_fun_" || fn.startsWith "modifier_"

mutual
  private partial def collectCalleesFromExpr (e : Expr) (acc : Std.HashSet String) : Std.HashSet String :=
    match e with
    | .call fn args =>
        let acc := args.foldl (fun a x => collectCalleesFromExpr x a) acc
        if isInterestingInlineFnName fn then acc.insert fn else acc
    | _ => acc

  private partial def collectCalleesFromStmt (s : Stmt) (acc : Std.HashSet String) : Std.HashSet String :=
    match s with
    | .let_ _ rhs => collectCalleesFromExpr rhs acc
    | .letMany _ rhs => collectCalleesFromExpr rhs acc
    | .assign _ rhs => collectCalleesFromExpr rhs acc
    | .assignMany _ rhs => collectCalleesFromExpr rhs acc
    | .expr e => collectCalleesFromExpr e acc
    | .block ss => ss.foldl (fun a st => collectCalleesFromStmt st a) acc
    | .if_ cond thenStmts =>
        let acc := collectCalleesFromExpr cond acc
        thenStmts.foldl (fun a st => collectCalleesFromStmt st a) acc
    | .switch_ scrut cases def? =>
        let acc := collectCalleesFromExpr scrut acc
        let acc := cases.foldl (fun a c => c.2.foldl (fun a2 st => collectCalleesFromStmt st a2) a) acc
        def?.map (fun ds => ds.foldl (fun a2 st => collectCalleesFromStmt st a2) acc) |>.getD acc
    | .for_ init cond post body =>
        let acc := init.foldl (fun a st => collectCalleesFromStmt st a) acc
        let acc := collectCalleesFromExpr cond acc
        let acc := post.foldl (fun a st => collectCalleesFromStmt st a) acc
        body.foldl (fun a st => collectCalleesFromStmt st a) acc
    | _ => acc
end

private def effectsToSlotSets (effs : Array Effect) : Std.HashSet String × Std.HashSet String × Std.HashSet String :=
  Id.run do
    let mut rs : Std.HashSet String := {}
    let mut ws : Std.HashSet String := {}
    let mut bc : Std.HashSet String := {}
    for e in effs do
      match e with
      | .storageRead s => rs := rs.insert s!"{s}"
      | .storageWrite s => ws := ws.insert s!"{s}"
      | .storageReadDyn se =>
          if slotRefParse? se |>.isSome then
            rs := rs.insert se
      | .storageWriteDyn se =>
          if slotRefParse? se |>.isSome then
            ws := ws.insert se
      | .boundaryCall t => bc := bc.insert t
    return (rs, ws, bc)

def summaryOfBody (body : Array Stmt) : FnSummary :=
  let effs := expectedEffectsFromStmts envEmpty body
  let (rs, ws, bc) := effectsToSlotSets effs
  let callees := collectCalleesFromStmt (.block body) {}
  { reads := rs, writes := ws, boundaryCalls := bc, callees := callees }

structure SummaryContext where
  version : String := "bh.yultextmini.summary_context.v0"
  iterMax : Nat := 6
  iters : Nat := 0
  summaries : Std.HashMap String FnSummary := {}
  failures : Array (String × String) := #[]
  deriving Inhabited

def SummaryContext.toJson (c : SummaryContext) : Json :=
  let items :=
    c.summaries.toList.mergeSort (fun a b => a.1 < b.1) |>.map (fun (k, v) =>
      Json.mkObj [("fn", Json.str k), ("summary", v.toJson)])
  Json.mkObj
    [ ("version", Json.str c.version)
    , ("iterMax", Json.num c.iterMax)
    , ("iters", Json.num c.iters)
    , ("failures",
        Json.arr <|
          c.failures.map (fun (p : String × String) => Json.mkObj [("fn", Json.str p.1), ("error", Json.str p.2)]))
    , ("summaries", Json.arr items.toArray)
    ]

def buildSummaryContext (ir : String) (fnsAll : Array String) (iterMax : Nat := 6) : SummaryContext :=
  Id.run do
    let mut base : Std.HashMap String FnSummary := Std.HashMap.emptyWithCapacity (fnsAll.size + 1)
    let mut failures : Array (String × String) := #[]
    for fn in fnsAll do
      if !isInterestingInlineFnName fn then
        continue
      match parseFunctionBodyE ir fn with
      | .error e =>
          failures := failures.push (fn, e)
      | .ok body =>
          base := base.insert fn (summaryOfBody body)

    let mut cur := base
    let mut iters : Nat := 0
    for _ in [:iterMax] do
      iters := iters + 1
      let mut changed := false
      let mut next := cur
      for (fn, s0) in cur.toList do
        let mut combined := s0
        for callee in hsToSortedArray s0.callees do
          combined := combined.join (cur.getD callee {})
        if !(combined.eqv s0) then
          changed := true
        next := next.insert fn combined
      cur := next
      if !changed then
        break

    return { iterMax := iterMax, iters := iters, summaries := cur, failures := failures }

end HeytingLean.BountyHunter.Solc.YulTextMini
