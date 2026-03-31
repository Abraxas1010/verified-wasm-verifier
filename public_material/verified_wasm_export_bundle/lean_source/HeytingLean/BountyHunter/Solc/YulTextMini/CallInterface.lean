import Std
import Lean
import HeytingLean.BountyHunter.Solc.YulTextMini.Types
import HeytingLean.BountyHunter.Solc.YulTextMini.Parse
import HeytingLean.BountyHunter.Solc.YulTextMini.Effects
import HeytingLean.BountyHunter.AlgebraIR.SlotRef

/-!
# HeytingLean.BountyHunter.Solc.YulTextMini.CallInterface

Adapter-shaped contracts often have little/no storage mutation. Their security posture is
mostly about *how they call out* to other contracts.

This module extracts a deterministic summary of boundary calls (`call`, `staticcall`,
`delegatecall`, `callcode`) from Yul IR function bodies.

This is still heuristic, but unlike storage-delta checks it has non-zero coverage on
stateless adapters.
-/

namespace HeytingLean.BountyHunter.Solc.YulTextMini

open Std

structure BoundaryCall where
  kind : String
  target : String
  value : String
  args : Array String
  tags : Array String
  deriving Repr, Inhabited

structure CallRiskFlag where
  name : String
  weight : Nat
  evidence : String
  deriving Repr, Inhabited

def CallRiskFlag.toJson (f : CallRiskFlag) : Lean.Json :=
  Lean.Json.mkObj
    [ ("name", Lean.Json.str f.name)
    , ("weight", Lean.Json.num f.weight)
    , ("evidence", Lean.Json.str f.evidence)
    ]

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

private def exprHasSubstr (needle : String) (e : Expr) : Bool :=
  containsSubstr (exprRender e) needle

private def natBinOp? (fn : String) : Option (Nat → Nat → Nat) :=
  match fn with
  | "add" => some (· + ·)
  | "sub" => some (fun a b => a - b)
  | "mul" => some (· * ·)
  | "shl" => some (fun a b => b <<< a)
  | "shr" => some (fun a b => b >>> a)
  | "and" => some (fun a b => Nat.land a b)
  | "or" => some (fun a b => Nat.lor a b)
  | "xor" => some (fun a b => Nat.xor a b)
  | _ => none

private def substExprWithEnv (env : Env) (e : Expr) (fuel : Nat := 20) : Expr :=
  if fuel = 0 then
    e
  else
    match e with
    | .ident name =>
        match env.get? name with
        | none => e
        | some e' => substExprWithEnv env e' (fuel - 1)
    | .call fn args =>
        .call fn (args.map (fun a => substExprWithEnv env a (fuel - 1)))
    | other => other

private def constFoldNat? (env : Env) (e : Expr) (fuel : Nat := 30) : Option Nat :=
  if fuel = 0 then
    none
  else
    match substExprWithEnv env e fuel with
    | .nat n => some n
    | .call fn args =>
        match natBinOp? fn, args[0]?, args[1]? with
        | some op, some a, some b =>
            match constFoldNat? env a (fuel - 1), constFoldNat? env b (fuel - 1) with
            | some x, some y => some (op x y)
            | _, _ => none
        | _, _, _ => none
    | _ => none

private def classifyTarget (env : Env) (e : Expr) : Array String :=
  let e := substExprWithEnv env e 20
  let rec collectStorageSlotRefs (e : Expr) (acc : Array String) : Array String :=
    match e with
    | .call "sload" args =>
        match args[0]? with
        | some slotE =>
            let r := HeytingLean.BountyHunter.AlgebraIR.slotRefToString (slotRefOfExpr env slotE)
            acc.push r
        | none => acc
    | .call fn args =>
        if fn.startsWith "read_from_storage" || fn.startsWith "load_from_storage" then
          match args[0]? with
          | some slotE =>
              let acc := args.foldl (fun a x => collectStorageSlotRefs x a) acc
              let r := HeytingLean.BountyHunter.AlgebraIR.slotRefToString (slotRefOfExpr env slotE)
              acc.push r
          | none => args.foldl (fun a x => collectStorageSlotRefs x a) acc
        else
          args.foldl (fun a x => collectStorageSlotRefs x a) acc
    | _ => acc
  Id.run do
    let mut tags : Array String := #[]
    if (constFoldNat? env e).isSome then
      tags := tags.push "target=const"
    match e with
    | .call "caller" #[] =>
        tags := tags.push "target=cx.caller()"
    | .ident "caller" =>
        tags := tags.push "target=cx.caller"
    | .ident _ =>
        tags := tags.push "target=var"
    | _ => pure ()
    if (!tags.any (fun t => t = "target=cx.caller()" || t = "target=cx.caller")) && exprHasSubstr "caller" e then
      tags := tags.push "target=cx.caller_derived"
    if exprHasSubstr "calldataload" e then
      tags := tags.push "target=calldata_derived"
    if exprHasSubstr "sload" e || exprHasSubstr "mapping_index_access" e || exprHasSubstr "keccak" e ||
       exprHasSubstr "read_from_storage" e || exprHasSubstr "load_from_storage" e then
      tags := tags.push "target=storage_derived"
      let slots := collectStorageSlotRefs e #[]
      if let some r := slots[0]? then
        tags := tags.push s!"target_slotref={r}"
        if let some n := r.toNat? then
          tags := tags.push s!"target_slot={n}"
    if exprHasSubstr "origin" e then
      tags := tags.push "target=tx.origin_derived"
    if exprHasSubstr "address" e || exprHasSubstr "this" e then
      tags := tags.push "target=addr_like"
    return tags

private def classifyValue (env : Env) (e : Expr) : Array String :=
  let e := substExprWithEnv env e 20
  Id.run do
    let mut tags : Array String := #[]
    match constFoldNat? env e with
    | some 0 => tags := tags.push "value=zero_const"
    | some _ => tags := tags.push "value=nonzero_const"
    | none => pure ()
    if exprHasSubstr "callvalue" e then
      tags := tags.push "value=callvalue"
    -- If we can't const-fold the value and it's not literally `callvalue`, treat it as
    -- *potentially nonzero* (e.g. storage-derived `bal`, calldata-derived amount).
    if (constFoldNat? env e).isNone && !(tags.any (· = "value=callvalue")) then
      tags := tags.push "value=nonzero_maybe"
    if tags.isEmpty then
      tags := tags.push "value=unknown"
    return tags

private def classifyCalldata (kind : String) (args : Array Expr) : Array String :=
  let argStrs := args.map exprRender
  let blob := String.intercalate "," argStrs.toList
  Id.run do
    let mut tags : Array String := #[]
    if argStrs.any (fun a => containsSubstr a "calldatacopy" || containsSubstr a "calldataload" || containsSubstr a "calldatasize") then
      tags := tags.push "calldata=calldata_derived"
    if argStrs.any (fun a => containsSubstr a "abi_encode") then
      tags := tags.push "calldata=abi_encode"
    if containsSubstr blob "calldataload(0" || containsSubstr blob "calldataload(0x0" then
      tags := tags.push "selector=calldata_derived"
    if containsSubstr blob "0x095ea7b3" then
      tags := tags.push "selector=approve"
    if containsSubstr blob "0x23b872dd" then
      tags := tags.push "selector=transferFrom"
    if kind = "call" || kind = "staticcall" || kind = "delegatecall" || kind = "callcode" then
      pure ()
    else
      tags := tags.push "calldata=unknown"
    return tags

private def mkCall (env : Env) (kind : String) (args : Array Expr) (targetIdx valueIdx : Nat) : BoundaryCall :=
  let targetE := args[targetIdx]?.getD (.ident "<missing_target>")
  let valueE :=
    if kind = "call" || kind = "callcode" then
      args[valueIdx]?.getD (.ident "<missing_value>")
    else
      (.nat 0)
  let tags := classifyTarget env targetE ++ classifyValue env valueE ++ classifyCalldata kind args
  { kind := kind
    target := exprRender targetE
    value := exprRender valueE
    args := args.map exprRender
    tags :=
      tags ++
      (if kind = "delegatecall" || kind = "callcode" then #["danger=delegate_like"] else #[])
  }

private def callsFromExpr (env : Env) (e : Expr) : Array BoundaryCall :=
  match e with
  | .call fn args =>
      let nested := args.foldl (fun acc a => acc ++ callsFromExpr env a) #[]
      let mine : Array BoundaryCall :=
        match fn with
        | "call" =>
            -- call(gas, addr, value, inPtr, inLen, outPtr, outLen)
            if args.size ≥ 3 then #[mkCall env "call" args 1 2] else #[]
        | "staticcall" =>
            -- staticcall(gas, addr, inPtr, inLen, outPtr, outLen) (no value)
            if args.size ≥ 2 then #[mkCall env "staticcall" args 1 0] else #[]
        | "delegatecall" =>
            -- delegatecall(gas, addr, inPtr, inLen, outPtr, outLen) (no value)
            if args.size ≥ 2 then #[mkCall env "delegatecall" args 1 0] else #[]
        | "callcode" =>
            if args.size ≥ 3 then #[mkCall env "callcode" args 1 2] else #[]
        | _ => #[]
      nested ++ mine
  | _ => #[]

mutual
  partial def collectCallsFromStmt (env : Env) (s : Stmt) : Array BoundaryCall :=
    match s with
    | .let_ _ rhs => callsFromExpr env rhs
    | .letMany _ rhs => callsFromExpr env rhs
    | .assign _ rhs => callsFromExpr env rhs
    | .assignMany _ rhs => callsFromExpr env rhs
    | .expr e => callsFromExpr env e
    | .block ss => collectCallsFromStmts env ss
    | .if_ cond thenStmts =>
        callsFromExpr env cond ++ collectCallsFromStmts env thenStmts
    | .switch_ scrut cases def? =>
        let fromCases :=
          cases.foldl (fun acc c => acc ++ collectCallsFromStmts env c.2) #[]
        let fromDef :=
          match def? with
          | none => #[]
          | some ss => collectCallsFromStmts env ss
        callsFromExpr env scrut ++ fromCases ++ fromDef
    | .for_ init cond post body =>
        let initC := collectCallsFromStmts env init
        let env2 := init.foldl (fun e st => updateEnv e st) env
        initC ++ callsFromExpr env2 cond ++ collectCallsFromStmts env2 post ++ collectCallsFromStmts env2 body
    | .break => #[]
    | .continue => #[]
    | .return_ _ => #[]
    | .revert _ => #[]
    | .leave => #[]

  partial def collectCallsFromStmts (env0 : Env) (ss : Array Stmt) : Array BoundaryCall :=
    Id.run do
      let mut env := env0
      let mut out : Array BoundaryCall := #[]
      for s in ss do
        out := out ++ collectCallsFromStmt env s
        env := updateEnv env s
      pure out
end

def BoundaryCall.toJson (c : BoundaryCall) : Lean.Json :=
  Lean.Json.mkObj
    [ ("kind", Lean.Json.str c.kind)
    , ("target", Lean.Json.str c.target)
    , ("value", Lean.Json.str c.value)
    , ("args", Lean.Json.arr (c.args.map Lean.Json.str))
    , ("tags", Lean.Json.arr (c.tags.map Lean.Json.str))
    ]

def scanIRBoundaryCalls (ir : String) (fn : String) : Except String (Array BoundaryCall) := do
  let body ← HeytingLean.BountyHunter.Solc.YulTextMini.parseFunctionBodyE ir fn
  return collectCallsFromStmts envEmpty body

private partial def stmtHasAbort : Stmt → Bool
  | .revert _ => true
  | .leave => true
  | .return_ _ => true
  | .block ss => ss.any stmtHasAbort
  | .if_ _ ss => ss.any stmtHasAbort
  | .switch_ _ cases def? =>
      let fromCases := cases.any (fun c => c.2.any stmtHasAbort)
      let fromDef := def?.map (·.any stmtHasAbort) |>.getD false
      fromCases || fromDef
  | .for_ init _ post body => init.any stmtHasAbort || post.any stmtHasAbort || body.any stmtHasAbort
  | _ => false

private def findSubstrIdx? (hay needle : String) : Option Nat :=
  if needle.isEmpty then
    some 0
  else if hay.length < needle.length then
    none
  else
    Id.run do
      let max := hay.length - needle.length
      for i in [:max.succ] do
        if (hay.drop i).startsWith needle then
          return some i
      return none

private def parseReturnVarName? (ir : String) (fnName : String) : Option String :=
  -- Best-effort parse of the Yul function header:
  --   function <fn>(...) -> <ret> { ... }
  -- Return the first identifier after `->`, trimmed.
  let needle := s!"function {fnName}("
  let i := findSubstrIdx? ir needle
  match i with
  | none => none
  | some idx =>
      -- Only scan a small window: the full header is short but `ir` can be huge.
      let tail := (ir.drop idx).take 2048
      -- restrict to the header line (up to `{`)
      let hdr :=
        match tail.splitOn "{" with
        | [] => tail
        | h :: _ => h
      if !containsSubstr hdr "->" then
        none
      else
        match hdr.splitOn "->" with
        | _ :: rhs :: _ =>
            let rhs := rhs.trim
            let tok := rhs.split (fun c => c = ' ' || c = '\n' || c = '\t' || c = '\r') |>.getD 0 ""
            if tok.isEmpty then none else some tok
        | _ => none

private def condChecksVar (v : String) (cond : Expr) : Bool :=
  match cond with
  | Expr.call "iszero" args =>
      match args[0]? with
      | some (Expr.ident nm) => nm = v
      | _ => containsSubstr (exprRender cond) v
  | Expr.ident nm => nm = v
  | _ => containsSubstr (exprRender cond) v

structure CallSite where
  call : BoundaryCall
  kind : String
  targetTags : Array String
  valueTags : Array String
  resultVar? : Option String := none
  ignoredReturn : Bool := false
  checked : Bool := false
  stmtIdx : Nat := 0
  raw : String := ""
  deriving Repr, Inhabited

private def boundaryCallAtTop? (env : Env) (e : Expr) : Option (String × Array Expr × BoundaryCall) :=
  match substExprWithEnv env e 20 with
  | .call fn args =>
      match fn with
      | "call" =>
          if args.size ≥ 3 then
            let c := mkCall env "call" args 1 2
            some ("call", args, c)
          else none
      | "staticcall" =>
          if args.size ≥ 2 then
            let c := mkCall env "staticcall" args 1 0
            some ("staticcall", args, c)
          else none
      | "delegatecall" =>
          if args.size ≥ 2 then
            let c := mkCall env "delegatecall" args 1 0
            some ("delegatecall", args, c)
          else none
      | "callcode" =>
          if args.size ≥ 3 then
            let c := mkCall env "callcode" args 1 2
            some ("callcode", args, c)
          else none
      | _ => none
  | _ => none

private def splitTags (tags : Array String) : Array String × Array String :=
  -- Preserve target provenance plus slot-ref evidence so downstream scoring can distinguish
  -- storage-derived targets (slot/slotref) from opaque variables.
  let ts := tags.filter (fun t => t.startsWith "target=" || t.startsWith "target_slot=" || t.startsWith "target_slotref=")
  let vs := tags.filter (fun t => t.startsWith "value=")
  (ts, vs)

private partial def collectAbortGuards (s : Stmt) (acc : Array String) : Array String :=
  match s with
  | .if_ cond thenStmts =>
      let acc :=
        if stmtHasAbort (.block thenStmts) then
          acc.push (exprRender cond)
        else
          acc
      thenStmts.foldl (fun a st => collectAbortGuards st a) acc
  | .switch_ scrut cases def? =>
      let hasAbort :=
        cases.any (fun c => c.2.any stmtHasAbort) || (def?.map (·.any stmtHasAbort) |>.getD false)
      let acc :=
        if hasAbort then
          acc.push (exprRender scrut)
        else
          acc
      let acc := cases.foldl (fun a c => c.2.foldl (fun a2 st => collectAbortGuards st a2) a) acc
      def?.map (fun ds => ds.foldl (fun a2 st => collectAbortGuards st a2) acc) |>.getD acc
  | .block ss => ss.foldl (fun a st => collectAbortGuards st a) acc
  | .for_ init cond post body =>
      let acc := init.foldl (fun a st => collectAbortGuards st a) acc
      let acc := acc.push (exprRender cond)
      let acc := post.foldl (fun a st => collectAbortGuards st a) acc
      body.foldl (fun a st => collectAbortGuards st a) acc
  | _ => acc

private partial def hasCalldataLenGuard (ss : Array Stmt) : Bool :=
  let condLooksLikeLenGuard (env : Env) (cond : Expr) : Bool :=
    let c := exprRender (substExprWithEnv env cond 20)
    containsSubstr c "calldatasize" && (containsSubstr c "lt" || containsSubstr c "gt" || containsSubstr c "eq")
  let exprLooksLikeLenGuard (env : Env) (e : Expr) : Bool :=
    let c := exprRender (substExprWithEnv env e 20)
    containsSubstr c "calldatasize" && (containsSubstr c "lt(" || containsSubstr c "gt(" || containsSubstr c "eq(")
  let rec go (env : Env) : Stmt → Bool
    | .if_ cond thenStmts => condLooksLikeLenGuard env cond || thenStmts.any (go env)
    | .block xs =>
        Id.run do
          let mut e := env
          let mut found := false
          for st in xs do
            if (!found) && go e st then
              found := true
            e := updateEnv e st
          return found
    | .switch_ scrut cases def? =>
        condLooksLikeLenGuard env scrut ||
          cases.any (fun x => x.2.any (go env)) ||
          (def?.map (·.any (go env)) |>.getD false)
    | .for_ init cond post body =>
        let initHas := init.any (go env)
        let env2 := init.foldl (fun e st => updateEnv e st) env
        initHas || condLooksLikeLenGuard env2 cond || post.any (go env2) || body.any (go env2)
    | .let_ _ rhs => exprLooksLikeLenGuard env rhs
    | .letMany _ rhs => exprLooksLikeLenGuard env rhs
    | .assign _ rhs => exprLooksLikeLenGuard env rhs
    | .assignMany _ rhs => exprLooksLikeLenGuard env rhs
    | .expr e => exprLooksLikeLenGuard env e
    | _ => false
  go envEmpty (.block ss)

private partial def hasAllowlistEvidence (ss : Array Stmt) : Bool :=
  let condLooksLikeAllowlist (env : Env) (cond : Expr) : Bool :=
    let c := exprRender (substExprWithEnv env cond 20)
    let hasStorageEvidence :=
      containsSubstr c "sload" ||
        containsSubstr c "read_from_storage" ||
        containsSubstr c "load_from_storage" ||
        containsSubstr c "mapping_index_access" ||
        containsSubstr c "keccak"
    let eqStyle := containsSubstr c "eq(" && hasStorageEvidence
    let mappingGuardStyle := hasStorageEvidence && (containsSubstr c "mapping_index_access" || containsSubstr c "keccak")
    eqStyle || mappingGuardStyle
  let exprLooksLikeAllowlist (env : Env) (e : Expr) : Bool :=
    let c := exprRender (substExprWithEnv env e 20)
    let hasStorageEvidence :=
      containsSubstr c "sload" ||
        containsSubstr c "read_from_storage" ||
        containsSubstr c "load_from_storage" ||
        containsSubstr c "mapping_index_access" ||
        containsSubstr c "keccak"
    let eqStyle := containsSubstr c "eq(" && hasStorageEvidence
    let mappingGuardStyle := hasStorageEvidence && (containsSubstr c "mapping_index_access" || containsSubstr c "keccak")
    eqStyle || mappingGuardStyle
  let rec go (env : Env) : Stmt → Bool
    | .if_ cond thenStmts => condLooksLikeAllowlist env cond || thenStmts.any (go env)
    | .block xs =>
        Id.run do
          let mut e := env
          let mut found := false
          for st in xs do
            if (!found) && go e st then
              found := true
            e := updateEnv e st
          return found
    | .switch_ scrut cases def? =>
        condLooksLikeAllowlist env scrut ||
          cases.any (fun x => x.2.any (go env)) ||
          (def?.map (·.any (go env)) |>.getD false)
    | .for_ init cond post body =>
        let initHas := init.any (go env)
        let env2 := init.foldl (fun e st => updateEnv e st) env
        initHas || condLooksLikeAllowlist env2 cond || post.any (go env2) || body.any (go env2)
    | .let_ _ rhs => exprLooksLikeAllowlist env rhs
    | .letMany _ rhs => exprLooksLikeAllowlist env rhs
    | .assign _ rhs => exprLooksLikeAllowlist env rhs
    | .assignMany _ rhs => exprLooksLikeAllowlist env rhs
    | .expr e => exprLooksLikeAllowlist env e
    | _ => false
  go envEmpty (.block ss)

private def isNonConstTarget (targetTags : Array String) : Bool :=
  targetTags.any (fun t =>
      t = "target=calldata_derived" ||
      t = "target=storage_derived" ||
      t = "target=tx.origin_derived" ||
      t = "target=cx.caller()" ||
      t = "target=cx.caller" ||
      t = "target=cx.caller_derived" ||
      t = "target=addr_like" ||
      t = "target=var") &&
    !(targetTags.any (· = "target=const"))

private def isExplicitDerivedTarget (targetTags : Array String) : Bool :=
  targetTags.any (fun t =>
    t = "target=calldata_derived" ||
    t = "target=storage_derived" ||
    t = "target=tx.origin_derived" ||
    t.startsWith "target_slot=" ||
    t.startsWith "target_slotref=")

private def isCallerTarget (targetTags : Array String) : Bool :=
  targetTags.any (fun t => t = "target=cx.caller()" || t = "target=cx.caller" || t = "target=cx.caller_derived")

private def isValueBearing (valueTags : Array String) : Bool :=
  valueTags.any (fun t => t = "value=nonzero_const" || t = "value=callvalue" || t = "value=nonzero_maybe")

private def isCalldataPassthroughCall (site : CallSite) : Bool :=
  if !(site.kind = "call" || site.kind = "staticcall") then
    false
  else
  let hasCalldataArg :=
    site.call.args.any (fun a => containsSubstr a "calldatacopy" || containsSubstr a "calldatasize" || containsSubstr a "calldataload")
  hasCalldataArg && site.targetTags.any (· = "target=calldata_derived")

private def isApproveLikeFn (fn : String) : Bool :=
  let f := fn.toLower
  containsSubstr f "approve"

private def isCommonApproveWrapperFn (fn : String) : Bool :=
  -- Suppress common library-style wrappers that accept a `spender` param but are not the
  -- right level of abstraction to blame (we want to flag the *caller* that selects the spender).
  let f := fn.toLower
  containsSubstr f "safeapprove" ||
    containsSubstr f "safe_approve" ||
    containsSubstr f "safetransfer" ||
    containsSubstr f "safetransferfrom"

private def isApproveCalldataDerived (site : CallSite) : Bool :=
  -- Extremely heuristic: encoded calldata includes `calldataload` in the argument construction.
  site.call.args.any (fun a => containsSubstr a "abi_encode" && containsSubstr a "calldataload")

private partial def stmtHasExprSubstr (needle : String) : Stmt → Bool
  | .let_ _ rhs => containsSubstr (exprRender rhs) needle
  | .letMany _ rhs => containsSubstr (exprRender rhs) needle
  | .assign _ rhs => containsSubstr (exprRender rhs) needle
  | .assignMany _ rhs => containsSubstr (exprRender rhs) needle
  | .expr e => containsSubstr (exprRender e) needle
  | .if_ cond thenStmts =>
      containsSubstr (exprRender cond) needle || thenStmts.any (stmtHasExprSubstr needle)
  | .switch_ scrut cases def? =>
      containsSubstr (exprRender scrut) needle ||
        cases.any (fun c => c.2.any (stmtHasExprSubstr needle)) ||
        (def?.map (fun ds => ds.any (stmtHasExprSubstr needle)) |>.getD false)
  | .for_ init cond post body =>
      init.any (stmtHasExprSubstr needle) ||
        containsSubstr (exprRender cond) needle ||
        post.any (stmtHasExprSubstr needle) ||
        body.any (stmtHasExprSubstr needle)
  | .block ss => ss.any (stmtHasExprSubstr needle)
  | .return_ args => containsSubstr (String.intercalate "," (args.toList.map exprRender)) needle
  | .revert args => containsSubstr (String.intercalate "," (args.toList.map exprRender)) needle
  | _ => false

private def scoreCallSites (fnName : String) (ss : Array Stmt) (topSites : Array CallSite) (allCalls : Array BoundaryCall) :
    Nat × Array CallRiskFlag :=
  Id.run do
    let mut flags : Array CallRiskFlag := #[]
    let mut score : Nat := 0
    let allSites : Array CallSite :=
      allCalls.map (fun c =>
        let (tt, vt) := splitTags c.tags
        { call := c, kind := c.kind, targetTags := tt, valueTags := vt })

    -- 1) Value-bearing call to a non-constant target.
    --
    -- We only treat this as *high-signal* when we have explicit provenance that the target is
    -- derived from calldata/storage (or a slot/slotref tag). Otherwise it’s often just the
    -- standard “send ETH to `to`” pattern (still relevant for reentrancy only when combined
    -- with write-after-call, which the CLI reports separately).
    let valueCalls :=
      topSites.filter (fun s =>
        s.kind = "call" && isValueBearing s.valueTags && isNonConstTarget s.targetTags)
    let callerValueCalls := valueCalls.filter (fun s => isCallerTarget s.targetTags)
    let derivedValueCalls := valueCalls.filter (fun s => isExplicitDerivedTarget s.targetTags && !isCallerTarget s.targetTags)
    if !derivedValueCalls.isEmpty then
      score := score + 10
      let ex := derivedValueCalls[0]?
      let ev := ex.map (fun s => s!"call value={s.call.value} target={s.call.target} tags={s.call.tags}") |>.getD "<example unavailable>"
      flags := flags.push { name := "value_bearing_call_to_nonconst_target", weight := 10, evidence := ev }
    else if !callerValueCalls.isEmpty then
      score := score + 4
      let ex := callerValueCalls[0]?
      let ev := ex.map (fun s => s!"call value={s.call.value} target={s.call.target} tags={s.call.tags}") |>.getD "<example unavailable>"
      flags := flags.push { name := "value_bearing_call_to_caller", weight := 4, evidence := ev }
    else if !valueCalls.isEmpty then
      -- Opaque `addr_like` / `var` targets without provenance: keep a low-weight flag so we can
      -- still rank and compose it with other evidence.
      let weight : Nat := if valueCalls.any (·.checked) then 4 else 6
      score := score + weight
      let ex := valueCalls[0]?
      let ev := ex.map (fun s => s!"call value={s.call.value} target={s.call.target} tags={s.call.tags}") |>.getD "<example unavailable>"
      flags := flags.push { name := "value_bearing_call_to_unknown_target", weight := weight, evidence := ev }

    -- 1b) Delegatecall/callcode to non-constant target (classic proxy footgun).
    --
    -- IMPORTANT: This signal is very FP-prone when we scan internal/library wrappers (e.g.
    -- OpenZeppelin `Address.functionDelegateCall`) because the wrapper’s `target` parameter
    -- looks like `target=var` even when every callsite passes `address(this)` (Multicall).
    --
    -- So we treat it as high-signal only when we have explicit provenance that the target is
    -- derived from calldata/storage (or we captured slot/slotref evidence). Otherwise we keep
    -- only a low-weight “unknown target” hint.
    let delegateLikes :=
      allSites.filter (fun s =>
        (s.kind = "delegatecall" || s.kind = "callcode") && !(s.targetTags.any (· = "target=const")))
    let derivedDelegateLikes := delegateLikes.filter (fun s => isExplicitDerivedTarget s.targetTags)
    let isSelectorDispatchTable (s : CallSite) : Bool :=
      s.targetTags.any (fun t =>
        t.startsWith "target_slotref=" && containsSubstr t "mapping_index_access" && containsSubstr t "calldataload(0")
    let dispatchDelegateLikes := derivedDelegateLikes.filter isSelectorDispatchTable
    if !dispatchDelegateLikes.isEmpty then
      -- Diamond/proxy dispatch is not a vulnerability by itself; keep as a low-weight tag
      -- so humans can see it without it dominating the ranking.
      score := score + 3
      let ex := dispatchDelegateLikes[0]?
      let ev := ex.map (fun s => s!"{s.kind} target={s.call.target} tags={s.call.tags}") |>.getD "<example unavailable>"
      flags := flags.push { name := "delegatecall_dispatch_table", weight := 3, evidence := ev }
    else if !derivedDelegateLikes.isEmpty then
      score := score + 9
      let ex := derivedDelegateLikes[0]?
      let ev := ex.map (fun s => s!"{s.kind} target={s.call.target} tags={s.call.tags}") |>.getD "<example unavailable>"
      flags := flags.push { name := "delegatecall_to_nonconst_target", weight := 9, evidence := ev }
    else if !delegateLikes.isEmpty then
      -- Keep a low-weight hint so the composed lead machinery can still surface
      -- “delegatecall + write-after-call” cases.
      score := score + 4
      let ex := delegateLikes[0]?
      let ev := ex.map (fun s => s!"{s.kind} target={s.call.target} tags={s.call.tags}") |>.getD "<example unavailable>"
      flags := flags.push { name := "delegatecall_to_unknown_target", weight := 4, evidence := ev }

    -- 2) Missing return-value check (ignored or never checked).
    let hasReturndataHandling :=
      ss.any (stmtHasExprSubstr "returndatasize") || ss.any (stmtHasExprSubstr "returndatacopy") || ss.any (stmtHasExprSubstr "extract_returndata")
    if (!hasReturndataHandling) && topSites.any (fun s => (!s.checked) && (s.kind = "call" || s.kind = "staticcall" || s.kind = "delegatecall" || s.kind = "callcode")) then
      score := score + 7
      let ex := topSites.find? (fun s => !s.checked)
      let ev :=
        ex.map (fun s =>
          let rv := s.resultVar?.getD ""
          s!"{s.kind} target={s.call.target} ignoredReturn={s.ignoredReturn} resultVar={rv}") |>.getD "<example unavailable>"
      flags := flags.push { name := "missing_return_value_check", weight := 7, evidence := ev }

    -- 3) Calldata passthrough without length validation.
    let hasGuard := hasCalldataLenGuard ss
    let hasCalldataEvidence :=
      ss.any (stmtHasExprSubstr "calldatacopy") || ss.any (stmtHasExprSubstr "calldataload") || ss.any (stmtHasExprSubstr "calldatasize")
    let isPassthroughLike (s : CallSite) : Bool :=
      (s.kind = "call" || s.kind = "staticcall") &&
        (isCalldataPassthroughCall s ||
          (hasCalldataEvidence && s.kind = "call" && !(s.targetTags.any (· = "target=const"))))
    if (!hasGuard) && allSites.any isPassthroughLike then
      score := score + 6
      let ex := allSites.find? isPassthroughLike
      let ev :=
        ex.map (fun s =>
          let a0 := s.call.args[0]?.getD ""
          let a1 := s.call.args[1]?.getD ""
          let a2 := s.call.args[2]?.getD ""
          s!"{s.kind} target={s.call.target} args0={a0} args1={a1} args2={a2}") |>.getD "<example unavailable>"
      flags := flags.push { name := "calldata_passthrough_no_len_guard", weight := 6, evidence := ev }

    -- 4) Token approval to calldata-derived spender (approx).
    if isApproveLikeFn fnName && !(isCommonApproveWrapperFn fnName) then
      let allowlisted := hasAllowlistEvidence ss
      let hasEffectfulCall := allSites.any (fun s => s.kind = "call")
      if (!allowlisted) && hasEffectfulCall then
        score := score + 8
        flags := flags.push
          { name := "approve_like_with_calldata_derived_address_no_allowlist_evidence"
            weight := 8
            evidence := "function name suggests approve; effectful call or calldata construction appears calldata-derived; no allowlist evidence detected"
          }

    return (score, flags)

private def writeEvidence? (e : HeytingLean.BountyHunter.AlgebraIR.Effect) : Option String :=
  match e with
  | .storageWrite slot => some s!"storageWrite(slot={slot})"
  | .storageWriteDyn se => some s!"storageWriteDyn(slotExpr={se})"
  | _ => none

private def isValueBearingCallToNonConstTarget (s : CallSite) : Bool :=
  let isCallLike := s.kind = "call" || s.kind = "callcode"
  let valueBearing :=
    s.valueTags.any (· = "value=callvalue") || s.valueTags.any (· = "value=nonzero_const") || s.valueTags.any (· = "value=nonzero_maybe")
  let nonConstTarget := !(s.targetTags.any (· = "target=const"))
  isCallLike && valueBearing && nonConstTarget

def scanIRCallInterfaceScoredWithWrites (ir : String) (fn : String) :
    Except String (Array BoundaryCall × Array CallSite × Nat × Array CallRiskFlag × Nat × Nat × Array String) := do
  let body ← HeytingLean.BountyHunter.Solc.YulTextMini.parseFunctionBodyE ir fn
  let retVar? := parseReturnVarName? ir fn
  let allCalls := collectCallsFromStmts envEmpty body
  -- Pass 1: collect call sites and env evolution (flat, deterministic).
  let mut env : Env := envEmpty
  let mut sites : Array CallSite := #[]
  for idx in [:body.size] do
    let s := body[idx]!
    match s with
    | .let_ name rhs =>
        match boundaryCallAtTop? env rhs with
        | some (k, _args, c) =>
            let (tt, vt) := splitTags c.tags
            sites := sites.push { call := c, kind := k, targetTags := tt, valueTags := vt, resultVar? := some name, ignoredReturn := false, checked := false, stmtIdx := idx, raw := exprRender rhs }
        | none => pure ()
        env := updateEnv env s
    | .letMany names rhs =>
        -- Best-effort: treat the first binder as the "success" result (when present).
        match names[0]? with
        | none =>
            env := updateEnv env s
        | some name =>
            match boundaryCallAtTop? env rhs with
            | some (k, _args, c) =>
                let (tt, vt) := splitTags c.tags
                sites :=
                  sites.push
                    { call := c
                      kind := k
                      targetTags := tt
                      valueTags := vt
                      resultVar? := some name
                      ignoredReturn := false
                      checked := false
                      stmtIdx := idx
                      raw := exprRender rhs
                    }
            | none => pure ()
            env := updateEnv env s
    | .assign name rhs =>
        match boundaryCallAtTop? env rhs with
        | some (k, _args, c) =>
            let (tt, vt) := splitTags c.tags
            sites := sites.push { call := c, kind := k, targetTags := tt, valueTags := vt, resultVar? := some name, ignoredReturn := false, checked := false, stmtIdx := idx, raw := exprRender rhs }
        | none => pure ()
        env := updateEnv env s
    | .assignMany names rhs =>
        match names[0]? with
        | none =>
            env := updateEnv env s
        | some name =>
            match boundaryCallAtTop? env rhs with
            | some (k, _args, c) =>
                let (tt, vt) := splitTags c.tags
                sites :=
                  sites.push
                    { call := c
                      kind := k
                      targetTags := tt
                      valueTags := vt
                      resultVar? := some name
                      ignoredReturn := false
                      checked := false
                      stmtIdx := idx
                      raw := exprRender rhs
                    }
            | none => pure ()
            env := updateEnv env s
    | .expr e =>
        match boundaryCallAtTop? env e with
        | some (k, _args, c) =>
            let (tt, vt) := splitTags c.tags
            sites := sites.push { call := c, kind := k, targetTags := tt, valueTags := vt, resultVar? := none, ignoredReturn := true, checked := false, stmtIdx := idx, raw := exprRender e }
        | none => pure ()
        env := updateEnv env s
    | _ =>
        env := updateEnv env s

  -- Pass 2: mark checked call return variables (best-effort within top-level body).
  let guards : Array String :=
    body.foldl (fun a st => collectAbortGuards st a) #[]

  let mut checkedVars : Std.HashSet String := {}
  for site in sites do
    match site.resultVar? with
    | none => pure ()
    | some v =>
        if let some rv := retVar? then
          if v = rv then
            checkedVars := checkedVars.insert v
        let mut usedLater := false
        for j in [(site.stmtIdx + 1):body.size] do
          if (!usedLater) && stmtHasExprSubstr v (body[j]!) then
            usedLater := true
        if usedLater || guards.any (fun g => containsSubstr g v) then
          checkedVars := checkedVars.insert v

  let sites2 :=
    sites.map (fun s =>
      match s.resultVar? with
      | some v =>
        if checkedVars.contains v then { s with checked := true } else s
      | none => s)

  let (score, flags) := scoreCallSites fn body sites2 allCalls
  -- Pass 3: approximate "write after risky call" composition for reentrancy-style leads.
  let mut riskyIdxs : Std.HashSet Nat := {}
  for s in sites2 do
    if isValueBearingCallToNonConstTarget s then
      riskyIdxs := riskyIdxs.insert s.stmtIdx

  let mut env2 : Env := envEmpty
  let mut writeStmtsAny : Nat := 0
  let mut writeStmtsAfterRisky : Nat := 0
  let mut writesAfterEv : Array String := #[]
  let mut seenRisky : Bool := false
  for idx in [:body.size] do
    let st := body[idx]!
    let ws := (expectedEffectsFromStmt env2 st).filterMap writeEvidence?
    if ws.size > 0 then
      writeStmtsAny := writeStmtsAny + 1
      if seenRisky then
        writeStmtsAfterRisky := writeStmtsAfterRisky + 1
        if writesAfterEv.size < 20 then
          writesAfterEv := writesAfterEv.push s!"stmtIdx={idx} {ws[0]!}"
    if riskyIdxs.contains idx then
      seenRisky := true
    env2 := updateEnv env2 st

  return (allCalls, sites2, score, flags, writeStmtsAny, writeStmtsAfterRisky, writesAfterEv)

def scanIRCallInterfaceScored (ir : String) (fn : String) :
    Except String (Array BoundaryCall × Array CallSite × Nat × Array CallRiskFlag) := do
  let (calls, sites, score, flags, _writesAny, _writesAfter, _writesAfterEv) ←
    scanIRCallInterfaceScoredWithWrites ir fn
  return (calls, sites, score, flags)

/-!
Phase 4 helper for temporal/cross-contract reasoning:

Count storage writes that occur **after any effectful boundary call** (call/delegatecall/callcode),
not just after the "value-bearing non-const" subset used for call-interface scoring.

This is intentionally coarse but stable and useful for:
- reentrancy-style checks (“call then write”),
- cross-contract “callback-capable callee + caller writes after call” heuristics.
-/
def scanIRWritesAfterAnyEffectfulCall (ir : String) (fn : String) :
    Except String (Nat × Array String) := do
  let (_calls, sites2, _score, _flags, _writesAny, _writesAfter, _writesAfterEv) ←
    scanIRCallInterfaceScoredWithWrites ir fn
  let effectfulIdxs : Array Nat :=
    sites2.filterMap (fun s =>
      if s.kind = "call" || s.kind = "delegatecall" || s.kind = "callcode" then
        some s.stmtIdx
      else
        none)
  if effectfulIdxs.isEmpty then
    return (0, #[])
  let firstCallIdx : Nat :=
    effectfulIdxs.foldl (fun m x => Nat.min m x) (effectfulIdxs[0]!)
  let body ← HeytingLean.BountyHunter.Solc.YulTextMini.parseFunctionBodyE ir fn
  let mut env2 : Env := envEmpty
  let mut writeStmtsAfterCall : Nat := 0
  let mut writesAfterEv : Array String := #[]
  for idx in [:body.size] do
    let st := body[idx]!
    let ws :=
      (expectedEffectsFromStmt env2 st).filterMap (fun e =>
        match e with
        | .storageWrite slot => some s!"storageWrite(slot={slot})"
        | .storageWriteDyn se => some s!"storageWriteDyn(slotExpr={se})"
        | _ => none)
    if ws.size > 0 then
      if idx > firstCallIdx then
        writeStmtsAfterCall := writeStmtsAfterCall + 1
        if writesAfterEv.size < 20 then
          writesAfterEv := writesAfterEv.push s!"stmtIdx={idx} {ws[0]!}"
    env2 := updateEnv env2 st
  return (writeStmtsAfterCall, writesAfterEv)

/-!
Best-effort guard detection used for suppressing false positives:

Return `true` when the function body contains an obvious `msg.data.length` / `calldatasize`
shape check that looks like a length guard.
-/
def scanIRHasCalldataLenGuard (ir : String) (fn : String) : Except String Bool := do
  let body ← HeytingLean.BountyHunter.Solc.YulTextMini.parseFunctionBodyE ir fn
  return hasCalldataLenGuard body

/-!
Phase 7 helper for temporal queries:

Detect whether there exists a **value-bearing storage-derived call** whose target is derived from a
storage slot ref `S`, and the function later writes to the *same* slot ref `S` (intraprocedural order).

This is intentionally coarse and best-effort; it is meant to support high-signal temporal atoms.
-/
def scanIRCallThenWriteSameSlotRef (ir : String) (fn : String) : Except String Bool := do
  let (_calls, sites2, _score, _flags, _writesAny, _writesAfter, _writesAfterEv) ←
    scanIRCallInterfaceScoredWithWrites ir fn
  let body ← HeytingLean.BountyHunter.Solc.YulTextMini.parseFunctionBodyE ir fn

  let tagSlotRef? (t : String) : Option String :=
    if t.startsWith "target_slotref=" then
      some (t.drop "target_slotref=".length)
    else
      none

  let isValueBearing (s : CallSite) : Bool :=
    s.valueTags.any (fun t => t = "value=nonzero_const" || t = "value=callvalue" || t = "value=nonzero_maybe")

  let isStorageDerived (s : CallSite) : Bool :=
    s.targetTags.any (· = "target=storage_derived")

  let mut writesByIdx : Std.HashMap Nat (Std.HashSet String) := {}
  let mut env2 : Env := envEmpty
  for idx in [:body.size] do
    let st := body[idx]!
    let mut ws : Std.HashSet String := {}
    for e in expectedEffectsFromStmt env2 st do
      match e with
      | .storageWrite slot => ws := ws.insert s!"{slot}"
      | .storageWriteDyn se => ws := ws.insert se
      | _ => pure ()
    if !ws.isEmpty then
      writesByIdx := writesByIdx.insert idx ws
    env2 := updateEnv env2 st

  for s in sites2 do
    if !(s.kind = "call" || s.kind = "callcode") then
      continue
    if !(isValueBearing s && isStorageDerived s) then
      continue
    match s.call.tags.findSome? tagSlotRef? with
    | none => continue
    | some slotRef =>
        let mut hit : Bool := false
        for idx in [(s.stmtIdx + 1):body.size] do
          if hit then
            continue
          let ws := writesByIdx.getD idx {}
          if ws.contains slotRef then
            hit := true
        if hit then
          return true
  return false

end HeytingLean.BountyHunter.Solc.YulTextMini
