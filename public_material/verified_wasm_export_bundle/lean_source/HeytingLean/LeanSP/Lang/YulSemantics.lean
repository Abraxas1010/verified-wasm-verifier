import HeytingLean.LeanSP.Lang.YulSyntax
import HeytingLean.LeanSP.Lang.EVMState
import HeytingLean.LeanSP.Lang.EVMPrimops

/-!
# LeanSP.Lang.YulSemantics

Fuel-bounded big-step operational semantics for Yul (EVM dialect).

**Termination:** All evaluation functions take a `fuel : Nat` parameter that
decreases on every recursive call through function boundaries. This guarantees
termination at runtime. The `partial` annotation is a concession to Lean 4's
termination checker, which cannot verify mutual recursion through monadic `for`
loops — it does NOT mean these functions can diverge. For any finite `fuel`,
execution terminates in finite time.

**Constraint H10:** The Hoare logic (Phase 4) MUST reference `execStmt`/`execBlock`
from THIS module — no separate evaluator.
-/

namespace LeanSP.Yul

open LeanSP.Arith
open LeanSP.EVM

mutual
/-- Evaluate a Yul expression to a list of Word256 values.
    Most expressions return exactly one value; function calls may return multiple. -/
partial def evalExpr (fuel : Nat) (e : Expr) (st : YulState) :
    Except ExecResult (List Word256 × YulState) :=
  match fuel with
  | 0 => .error .outOfFuel
  | fuel' + 1 =>
    match e with
    | .ident name =>
        match VarStore.get? st.vars name with
        | some val => .ok ([val], st)
        | none => .error (.invalid s!"undefined variable: {name}")
    | .nat n => .ok ([BitVec.ofNat 256 n], st)
    | .str _ => .ok ([Word256.zero], st)
    | .bool b => .ok ([if b then Word256.one else Word256.zero], st)
    | .call fn args => evalFuncCall fuel' fn args st

/-- Evaluate a function call (primop or user-defined function). -/
partial def evalFuncCall (fuel : Nat) (fn : String) (argExprs : Array Expr)
    (st : YulState) : Except ExecResult (List Word256 × YulState) :=
  match fuel with
  | 0 => .error .outOfFuel
  | fuel' + 1 => do
    -- Evaluate arguments left to right
    let mut argVals : List Word256 := []
    let mut curSt := st
    for argExpr in argExprs do
      let (vals, st') ← evalExpr fuel' argExpr curSt
      match vals with
      | [v] => argVals := argVals ++ [v]; curSt := st'
      | _ => throw (.invalid s!"argument expression returned {vals.length} values")
    -- Try primop first
    match evalPrimop fn argVals curSt with
    | some (vals, st') => .ok (vals, st')
    | none =>
      -- Try user-defined function
      match FuncStore.get? curSt.funcs fn with
      | some funcDef =>
          if argVals.length != funcDef.params.size then
            .error (.invalid s!"function {fn}: expected {funcDef.params.size} args, got {argVals.length}")
          else
            -- Bind params to args in a new scope
            let mut funcVars : VarStore := VarStore.empty
            for i in [:funcDef.params.size] do
              match funcDef.params[i]?, argVals[i]? with
              | some p, some v => funcVars := VarStore.insert funcVars p v
              | _, _ => pure ()
            -- Initialize return variables to 0
            for r in funcDef.returns do
              funcVars := VarStore.insert funcVars r Word256.zero
            let funcSt := { curSt with vars := funcVars }
            -- Execute function body
            match execBlock fuel' funcDef.body funcSt with
            | .ok st' | .error (.leave st') =>
                let retVals := funcDef.returns.toList.map
                  (fun r => VarStore.getD st'.vars r Word256.zero)
                pure (retVals, { st' with vars := curSt.vars })
            | .error (.return_ data st') =>
                let evm' := { st'.evm with returnData := data }
                pure ([], { st' with vars := curSt.vars, evm := evm' })
            | .error (.revert data st') =>
                .error (.revert data { st' with vars := curSt.vars })
            | .error e => .error e
      | none => .error (.invalid s!"unknown function: {fn}")

/-- Execute a block of statements sequentially. -/
partial def execBlock (fuel : Nat) (stmts : Array Stmt) (st : YulState) :
    Except ExecResult YulState :=
  match fuel with
  | 0 => .error .outOfFuel
  | fuel' + 1 => do
    let mut curSt := st
    for stmt in stmts do
      curSt ← execStmt fuel' stmt curSt
    .ok curSt

/-- Execute a single Yul statement. -/
partial def execStmt (fuel : Nat) (s : Stmt) (st : YulState) :
    Except ExecResult YulState :=
  match fuel with
  | 0 => .error .outOfFuel
  | fuel' + 1 =>
    match s with
    | .let_ name rhs => do
        let (vals, st') ← evalExpr fuel' rhs st
        match vals with
        | [v] => .ok { st' with vars := VarStore.insert st'.vars name v }
        | _ => .error (.invalid s!"let {name}: rhs returned {vals.length} values")
    | .letMany names rhs => do
        let (vals, st') ← evalExpr fuel' rhs st
        if vals.length != names.size then
          .error (.invalid s!"let multi: expected {names.size} values, got {vals.length}")
        else
          let mut curSt := st'
          for i in [:names.size] do
            match names[i]?, vals[i]? with
            | some n, some v => curSt := { curSt with vars := VarStore.insert curSt.vars n v }
            | _, _ => pure ()
          .ok curSt
    | .assign name rhs => do
        let (vals, st') ← evalExpr fuel' rhs st
        match vals with
        | [v] => .ok { st' with vars := VarStore.insert st'.vars name v }
        | _ => .error (.invalid s!"assign {name}: rhs returned {vals.length} values")
    | .assignMany names rhs => do
        let (vals, st') ← evalExpr fuel' rhs st
        if vals.length != names.size then
          .error (.invalid s!"assign multi: expected {names.size} values, got {vals.length}")
        else
          let mut curSt := st'
          for i in [:names.size] do
            match names[i]?, vals[i]? with
            | some n, some v => curSt := { curSt with vars := VarStore.insert curSt.vars n v }
            | _, _ => pure ()
          .ok curSt
    | .expr e => do
        let (_, st') ← evalExpr fuel' e st
        .ok st'
    | .if_ cond thenStmts => do
        let (vals, st') ← evalExpr fuel' cond st
        match vals with
        | [v] =>
            if v != Word256.zero then execBlock fuel' thenStmts st'
            else .ok st'
        | _ => .error (.invalid "if: condition returned multiple values")
    | .switch_ scrut cases default? => do
        let (vals, st') ← evalExpr fuel' scrut st
        match vals with
        | [v] =>
            let matched := cases.find? fun (lit, _) =>
              match lit with
              | .nat n => v == BitVec.ofNat 256 n
              | .bool b => v == (if b then Word256.one else Word256.zero)
              | .str _ => false
            match matched with
            | some (_, body) => execBlock fuel' body st'
            | none =>
                match default? with
                | some body => execBlock fuel' body st'
                | none => .ok st'
        | _ => .error (.invalid "switch: scrutinee returned multiple values")
    | .for_ init cond post body =>
        execForLoop fuel' init cond post body st
    | .block stmts => execBlock fuel' stmts st
    | .break => .error (.break_ st)
    | .continue => .error (.continue' st)
    | .return_ args => do
        if args.isEmpty then .error (.return_ ByteArray.empty st)
        else
          let mut retVals : List Word256 := []
          let mut curSt := st
          for arg in args do
            let (vals, st') ← evalExpr fuel' arg curSt
            retVals := retVals ++ vals; curSt := st'
          match retVals with
          | [off, sz] =>
              let (_, mem) := curSt.evm.memory.mload off.toNat
              let data := mem.data.extract off.toNat (off.toNat + sz.toNat)
              .error (.return_ data { curSt with evm := { curSt.evm with memory := mem } })
          | _ => .error (.return_ ByteArray.empty curSt)
    | .revert args => do
        if args.isEmpty then .error (.revert ByteArray.empty st)
        else
          let mut retVals : List Word256 := []
          let mut curSt := st
          for arg in args do
            let (vals, st') ← evalExpr fuel' arg curSt
            retVals := retVals ++ vals; curSt := st'
          match retVals with
          | [off, sz] =>
              let (_, mem) := curSt.evm.memory.mload off.toNat
              let data := mem.data.extract off.toNat (off.toNat + sz.toNat)
              .error (.revert data { curSt with evm := { curSt.evm with memory := mem } })
          | _ => .error (.revert ByteArray.empty curSt)
    | .leave => .error (.leave st)

/-- Execute a Yul `for` loop: `for { init } cond { post } { body }` -/
partial def execForLoop (fuel : Nat) (init : Array Stmt) (cond : Expr)
    (post : Array Stmt) (body : Array Stmt) (st : YulState) :
    Except ExecResult YulState :=
  match fuel with
  | 0 => .error .outOfFuel
  | fuel' + 1 => do
    let st' ← execBlock fuel' init st
    forLoopIter fuel' cond post body st'

/-- Execute one iteration of a for loop and recurse. -/
partial def forLoopIter (fuel : Nat) (cond : Expr) (post : Array Stmt)
    (body : Array Stmt) (st : YulState) : Except ExecResult YulState :=
  match fuel with
  | 0 => .error .outOfFuel
  | fuel' + 1 => do
    let (vals, st') ← evalExpr fuel' cond st
    match vals with
    | [v] =>
        if v == Word256.zero then .ok st'
        else
          match execBlock fuel' body st' with
          | .ok st'' => do
              let st''' ← execBlock fuel' post st''
              forLoopIter fuel' cond post body st'''
          | .error (.break_ st'') => .ok st''
          | .error (.continue' st'') => do
              let st''' ← execBlock fuel' post st''
              forLoopIter fuel' cond post body st'''
          | .error e => .error e
    | _ => .error (.invalid "for loop: condition returned multiple values")

end

end LeanSP.Yul
