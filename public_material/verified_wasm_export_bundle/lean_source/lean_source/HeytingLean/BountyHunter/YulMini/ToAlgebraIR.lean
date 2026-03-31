import HeytingLean.BountyHunter.YulMini.Types
import HeytingLean.BountyHunter.AlgebraIR.Types

/-!
# HeytingLean.BountyHunter.YulMini.ToAlgebraIR

Phase 1 translator: YulMini AST → AlgebraIR control-flow graph (CFG) suitable
for dominance-style checks.

This translator is intentionally conservative:
- it ignores dataflow beyond tagging effects
- it builds a deterministic CFG from structured control flow
- it stops translation at the first unreachable statement in a block
-/

namespace HeytingLean.BountyHunter.YulMini

open HeytingLean.BountyHunter.AlgebraIR

structure BuildState where
  nextId : Nat := 0
  nodes : Array (NodeId × String × Array Effect) := #[]
  succs : Array (Array NodeId) := #[]
  exits : Array NodeId := #[]
  deriving Inhabited

private def freshId : BuildState → (NodeId × BuildState)
  | st =>
      let id := st.nextId
      (id, { st with nextId := id + 1, succs := st.succs.push #[] })

private def addNode (tag : String) (effects : Array Effect) : BuildState → (NodeId × BuildState)
  | st =>
      let (id, st) := freshId st
      (id, { st with nodes := st.nodes.push (id, tag, effects) })

private def addExit (id : NodeId) (st : BuildState) : BuildState :=
  { st with exits := st.exits.push id }

private def addEdge (src dst : NodeId) : BuildState → BuildState
  | st =>
      let cur := st.succs[src]!
      { st with succs := st.succs.set! src (cur.push dst) }

private def effectsOfExpr : Expr → Array Effect
  | .var _ => #[]
  | .nat _ => #[]
  | .builtin b args =>
      let eff :=
        match b with
        | .sload slot => #[Effect.storageRead slot]
        | .sstore slot => #[Effect.storageWrite slot]
        | .call target => #[Effect.boundaryCall target]
      eff ++ (args.foldl (fun acc e => acc ++ effectsOfExpr e) #[])

private def effectsOfStmt : Stmt → Array Effect
  | .let_ _ e => effectsOfExpr e
  | .expr e => effectsOfExpr e
  | .if_ c _ _ => effectsOfExpr c
  | .return_ => #[]
  | .revert => #[]

structure BlockResult where
  entry? : Option NodeId
  fallthrough : Array NodeId
  deriving Inhabited

private partial def buildStmts (stmts : Array Stmt) (st : BuildState) : (BlockResult × BuildState) :=
  Id.run do
    let mut st := st
    let mut entry? : Option NodeId := none
    let mut pending : Array NodeId := #[]
    let mut live := true
    for s in stmts do
      if !live then
        break
      let (res, st') := buildStmt s st
      st := st'
      match res.entry? with
      | none =>
          -- Empty/unreachable statement: stop.
          live := false
      | some entry =>
          if entry?.isNone then
            entry? := some entry
          for p in pending do
            st := addEdge p entry st
          pending := res.fallthrough
          if pending.isEmpty then
            -- From this point, the block is terminated; remaining statements are unreachable.
            live := false
    return ({ entry? := entry?, fallthrough := pending }, st)
where
  buildStmt : Stmt → BuildState → (BlockResult × BuildState)
    | .let_ x e, st =>
        let (id, st) := addNode s!"let {x}" (effectsOfExpr e) st
        ({ entry? := some id, fallthrough := #[id] }, st)
    | .expr e, st =>
        let (id, st) := addNode "expr" (effectsOfExpr e) st
        ({ entry? := some id, fallthrough := #[id] }, st)
    | .return_, st =>
        let (id, st) := addNode "return" #[] st
        ({ entry? := some id, fallthrough := #[] }, addExit id st)
    | .revert, st =>
        let (id, st) := addNode "revert" #[] st
        ({ entry? := some id, fallthrough := #[] }, addExit id st)
    | .if_ cond then_ else_, st =>
        Id.run do
          let (condId, st) := addNode "if" (effectsOfExpr cond) st
          let (thenRes, st) := buildStmts then_ st
          let (elseRes, st) := buildStmts else_ st
          let (joinId, st) := addNode "join" #[] st
          let mut st := st
          -- cond → then/else (or directly to join if branch empty)
          match thenRes.entry? with
          | some tEntry => st := addEdge condId tEntry st
          | none => st := addEdge condId joinId st
          match elseRes.entry? with
          | some eEntry => st := addEdge condId eEntry st
          | none => st := addEdge condId joinId st
          -- branch fallthroughs → join
          for x in thenRes.fallthrough do
            st := addEdge x joinId st
          for x in elseRes.fallthrough do
            st := addEdge x joinId st
          return ({ entry? := some condId, fallthrough := #[joinId] }, st)

private def finalize (entry : NodeId) (st : BuildState) : Graph :=
  let nodes : Array Node :=
    st.nodes.map (fun (id, tag, eff) =>
      { id := id
        op := { tag := tag }
        args := #[]
        effects := eff
        succs := st.succs[id]!
      })
  { entry := entry, exits := st.exits, nodes := nodes }

def translateFunc (f : Func) : Graph :=
  let st0 : BuildState := {}
  let (res, st1) := buildStmts f.body st0
  match res.entry? with
  | none =>
      let (rid, st2) := addNode "return" #[] st1
      finalize rid (addExit rid st2)
  | some entry =>
      if res.fallthrough.isEmpty then
        finalize entry st1
      else
        let (rid, st2) := addNode "return" #[] st1
        let st3 := addExit rid st2
        let st4 := res.fallthrough.foldl (fun st n => addEdge n rid st) st3
        finalize entry st4

def translateProgram (p : Program) (funcName : String := "withdraw") : Except String Graph := do
  match p.funcs.find? (fun f => f.name = funcName) with
  | none => .error s!"no function named '{funcName}'"
  | some f => .ok (translateFunc f)

end HeytingLean.BountyHunter.YulMini
