import Std
import HeytingLean.BountyHunter.Solc.YulTextMini.Types

/-!
# HeytingLean.BountyHunter.Solc.YulTextMini.Risk

Lightweight, deterministic “risk scan” over the parsed YulTextMini AST.

This is intentionally conservative and *non-proving*:
- it never upgrades a contract to SAFE,
- it only records the presence of potentially dangerous primitives/patterns,
  so downstream tooling can decide how to treat them (warn, OUT_OF_SCOPE, etc.).
-/

namespace HeytingLean.BountyHunter.Solc.YulTextMini

structure RiskReport where
  version : String := "yultextmini.risk.v0"
  boundaryTargets : Array String := #[]
  usesOrigin : Bool := false
  usesTimestamp : Bool := false
  usesBlockhash : Bool := false
  usesPrevrandao : Bool := false
  usesSelfdestruct : Bool := false
  usesDelegatecall : Bool := false
  usesCallcode : Bool := false
  usesCreate : Bool := false
  usesCreate2 : Bool := false
  uncheckedCallReturn : Bool := false
  deriving Repr, DecidableEq, Inhabited

private def insertUniqSorted (xs : Array String) : Array String :=
  let ys := xs.toList.eraseDups.mergeSort
  ys.toArray

private def addBoundary (r : RiskReport) (t : String) : RiskReport :=
  { r with boundaryTargets := (r.boundaryTargets.push t) }

private def isLowLevelCall (fn : String) : Bool :=
  fn = "call" || fn = "staticcall" || fn = "delegatecall" || fn = "callcode"

/-!
Detect “unchecked low-level call return values” conservatively.

Heuristic (v0, deterministic):
- If a `let x := call(...)` / `letMany` binds the return of a low-level call and `x`
  is never referenced later in the same statement list, mark as unchecked.
- Additionally, treat `pop(call(...))` as unchecked (handled in `scanExpr`).

This intentionally does *not* attempt full dataflow or control-flow reasoning.
-/
mutual
  private partial def eraseUsedInExpr (pending : Std.HashSet String) (e : Expr) : Std.HashSet String :=
    match e with
    | .ident n => pending.erase n
    | .nat _ => pending
    | .str _ => pending
    | .bool _ => pending
    | .call _ args => args.foldl (fun acc a => eraseUsedInExpr acc a) pending

  private partial def eraseUsedInStmt (pending : Std.HashSet String) (s : Stmt) : Std.HashSet String :=
    match s with
    | .let_ _ rhs => eraseUsedInExpr pending rhs
    | .letMany _ rhs => eraseUsedInExpr pending rhs
    | .assign _ rhs => eraseUsedInExpr pending rhs
    | .assignMany _ rhs => eraseUsedInExpr pending rhs
    | .expr e => eraseUsedInExpr pending e
    | .if_ cond thenStmts =>
        eraseUsedInStmts (eraseUsedInExpr pending cond) thenStmts
    | .switch_ scrut cases def? =>
        let p := eraseUsedInExpr pending scrut
        let p := cases.foldl (fun acc c => eraseUsedInStmts acc c.2) p
        match def? with
        | none => p
        | some ss => eraseUsedInStmts p ss
    | .for_ init cond post body =>
        let p := eraseUsedInStmts pending init
        let p := eraseUsedInExpr p cond
        let p := eraseUsedInStmts p post
        eraseUsedInStmts p body
    | .break => pending
    | .continue => pending
    | .block ss => eraseUsedInStmts pending ss
    | .return_ args => args.foldl (fun acc a => eraseUsedInExpr acc a) pending
    | .revert args => args.foldl (fun acc a => eraseUsedInExpr acc a) pending
    | .leave => pending

  private partial def eraseUsedInStmts (pending : Std.HashSet String) (ss : Array Stmt) : Std.HashSet String :=
    ss.foldl (fun acc s => eraseUsedInStmt acc s) pending
end

private partial def uncheckedCallReturnInStmts (ss : Array Stmt) : Bool :=
  Id.run do
    let mut pending : Std.HashSet String := Std.HashSet.emptyWithCapacity 16
    for s in ss do
      pending := eraseUsedInStmt pending s
      match s with
      | .let_ name (.call fn _) =>
          if isLowLevelCall fn then
            pending := pending.insert name
          else
            pure ()
      | .letMany names (.call fn _) =>
          if isLowLevelCall fn then
            for n in names do
              pending := pending.insert n
          else
            pure ()
      | .assignMany names (.call fn _) =>
          if isLowLevelCall fn then
            for n in names do
              pending := pending.insert n
          else
            pure ()
      | _ => pure ()
    return !pending.isEmpty

mutual
  private partial def scanExpr (e : Expr) (r0 : RiskReport) : RiskReport :=
    match e with
    | .ident _ => r0
    | .nat _ => r0
    | .str _ => r0
    | .bool _ => r0
    | .call fn args =>
        let r := args.foldl (fun acc a => scanExpr a acc) r0
        match fn with
        | "origin" => { r with usesOrigin := true }
        | "timestamp" => { r with usesTimestamp := true }
        | "blockhash" => { r with usesBlockhash := true }
        | "prevrandao" => { r with usesPrevrandao := true }
        | "selfdestruct" => { addBoundary r "selfdestruct" with usesSelfdestruct := true }
        | "suicide" => { addBoundary r "selfdestruct" with usesSelfdestruct := true }
        | "delegatecall" => { addBoundary r "delegatecall" with usesDelegatecall := true }
        | "callcode" => { addBoundary r "callcode" with usesCallcode := true }
        | "call" => addBoundary r "call"
        | "staticcall" => addBoundary r "staticcall"
        | "create" => { addBoundary r "create" with usesCreate := true }
        | "create2" => { addBoundary r "create2" with usesCreate2 := true }
        | "pop" =>
            match args[0]? with
            | none => r
            | some e =>
                match e with
                | .call innerFn _ =>
                    if isLowLevelCall innerFn then
                      { r with uncheckedCallReturn := true }
                    else
                      r
                | _ => r
        | _ => r

  private partial def scanStmt (s : Stmt) (r0 : RiskReport) : RiskReport :=
    match s with
    | .let_ _ rhs => scanExpr rhs r0
    | .letMany _ rhs => scanExpr rhs r0
    | .assign _ rhs => scanExpr rhs r0
    | .assignMany _ rhs => scanExpr rhs r0
    | .expr e => scanExpr e r0
    | .if_ cond thenStmts =>
        scanStmts thenStmts (scanExpr cond r0)
    | .switch_ scrut cases def? =>
        let r := scanExpr scrut r0
        let r := cases.foldl (fun acc c => scanStmts c.2 acc) r
        match def? with
        | none => r
        | some ss => scanStmts ss r
    | .for_ init cond post body =>
        let r := scanStmts init r0
        let r := scanExpr cond r
        let r := scanStmts post r
        scanStmts body r
    | .break => r0
    | .continue => r0
    | .block ss => scanStmts ss r0
    | .return_ args => args.foldl (fun acc a => scanExpr a acc) r0
    | .revert args => args.foldl (fun acc a => scanExpr a acc) r0
    | .leave => r0

  partial def scanStmts (ss : Array Stmt) (r0 : RiskReport := {}) : RiskReport :=
    let r := ss.foldl (fun acc s => scanStmt s acc) r0
    if r.uncheckedCallReturn then
      r
    else
      { r with uncheckedCallReturn := uncheckedCallReturnInStmts ss }
end

def normalize (r : RiskReport) : RiskReport :=
  { r with boundaryTargets := insertUniqSorted r.boundaryTargets }

def riskToJson (r : RiskReport) : Lean.Json :=
  Lean.Json.mkObj
    [ ("version", Lean.Json.str r.version)
    , ("boundaryTargets", Lean.Json.arr (r.boundaryTargets.map Lean.Json.str))
    , ("usesOrigin", Lean.Json.bool r.usesOrigin)
    , ("usesTimestamp", Lean.Json.bool r.usesTimestamp)
    , ("usesBlockhash", Lean.Json.bool r.usesBlockhash)
    , ("usesPrevrandao", Lean.Json.bool r.usesPrevrandao)
    , ("usesSelfdestruct", Lean.Json.bool r.usesSelfdestruct)
    , ("usesDelegatecall", Lean.Json.bool r.usesDelegatecall)
    , ("usesCallcode", Lean.Json.bool r.usesCallcode)
    , ("usesCreate", Lean.Json.bool r.usesCreate)
    , ("usesCreate2", Lean.Json.bool r.usesCreate2)
    , ("uncheckedCallReturn", Lean.Json.bool r.uncheckedCallReturn)
    ]

end HeytingLean.BountyHunter.Solc.YulTextMini
