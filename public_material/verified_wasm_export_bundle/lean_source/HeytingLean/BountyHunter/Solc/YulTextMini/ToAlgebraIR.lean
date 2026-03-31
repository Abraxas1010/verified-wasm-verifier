import Std
import HeytingLean.BountyHunter.Solc.YulTextMini.Types
import HeytingLean.BountyHunter.Solc.YulTextMini.Effects
import HeytingLean.BountyHunter.AlgebraIR.Types

/-!
# HeytingLean.BountyHunter.Solc.YulTextMini.ToAlgebraIR

Translate a parsed Yul-text function body (minimal subset) into an AlgebraIR CFG.

This is deliberately conservative: if the source uses unsupported constructs
that would change control-flow in a way we do not model, callers should treat
the result as `OUT_OF_SCOPE` rather than relying on it for correctness.
-/

namespace HeytingLean.BountyHunter.Solc.YulTextMini

open HeytingLean.BountyHunter.AlgebraIR

abbrev EffectsFn := Env → Expr → Array Effect

private def sortDedupNat (xs : Array Nat) : Array Nat :=
  Id.run do
    let ys := xs.qsort (fun a b => a < b)
    let mut out : Array Nat := #[]
    for x in ys do
      match out.back? with
      | none => out := out.push x
      | some y =>
          if x = y then
            continue
          else
            out := out.push x
    return out

private structure Builder where
  nodes : Array Node := #[]
  env : Env := envEmpty

private def mkNode (b : Builder) (tag : String) (effects : Array Effect) : Builder × NodeId :=
  let id := b.nodes.size
  let n : Node :=
    { id := id
      op := { tag := tag }
      args := #[]
      effects := effects
      succs := #[] }
  ({ nodes := b.nodes.push n, env := b.env }, id)

private def setSuccs (b : Builder) (id : NodeId) (succs : Array NodeId) : Builder :=
  if id < b.nodes.size then
    let n := b.nodes[id]!
    let n' := { n with succs := succs }
    { nodes := b.nodes.set! id n', env := b.env }
  else
    b

private def connectExits (b : Builder) (exits : Array NodeId) (next : NodeId) : Builder :=
  exits.foldl (fun b id => setSuccs b id #[next]) b

private structure LoopCtx where
  breakTarget : NodeId
  continueTarget : NodeId

mutual
  private partial def buildStmts (effectsFn : EffectsFn) (ctx? : Option LoopCtx) (b : Builder) (ss : Array Stmt) :
      Except String (Builder × Option NodeId × Array NodeId) := do
    let mut b := b
    let mut entry : Option NodeId := none
    let mut openExits : Array NodeId := #[]
    for s in ss do
      let (b2, sEntry, sExits) ← buildStmt effectsFn ctx? b s
      b := b2
      match entry with
      | none => entry := some sEntry
      | some _ =>
          b := connectExits b openExits sEntry
      openExits := sExits
    pure (b, entry, openExits)

  private partial def buildStmt (effectsFn : EffectsFn) (ctx? : Option LoopCtx) (b : Builder) (s : Stmt) :
      Except String (Builder × NodeId × Array NodeId) := do
    match s with
    | .let_ name rhs =>
        let (b, id) := mkNode b s!"let {name}" (effectsFn b.env rhs)
        let b := { b with env := b.env.insert name rhs }
        pure (b, id, #[id])
    | .letMany names rhs =>
        let lhs := String.intercalate "," names.toList
        let tag := s!"let {lhs}"
        let (b, id) := mkNode b tag (effectsFn b.env rhs)
        let env' :=
          match names[0]?, names[1]?, rhs with
          | some a, some b2, .call fn args =>
              if (fn.splitOn "storage_array_index_access").length > 1 then
                match args[0]?, args[1]? with
                | some baseE, some idxE =>
                    let baseE :=
                      if (fn.splitOn "$dyn_storage").length > 1 then
                        .call "keccak" #[baseE]
                      else
                        baseE
                    b.env.insert a (.call "add" #[baseE, idxE]) |>.insert b2 (.nat 0)
                | _, _ => b.env
              else
                b.env
          | _, _, _ => b.env
        let b := { b with env := env' }
        pure (b, id, #[id])
    | .assign name rhs =>
        let (b, id) := mkNode b s!"assign {name}" (effectsFn b.env rhs)
        let b := { b with env := b.env.insert name rhs }
        pure (b, id, #[id])
    | .assignMany names rhs =>
        let lhs := String.intercalate "," names.toList
        let (b, id) := mkNode b s!"assign {lhs}" (effectsFn b.env rhs)
        let env' := names.foldl (fun e n => e.erase n) b.env
        let b := { b with env := env' }
        pure (b, id, #[id])
    | .expr e =>
        let tag :=
          match e with
          | .call fn _ => s!"call {fn}"
          | .ident x => s!"ident {x}"
          | .nat n => s!"nat {n}"
          | .str s => s!"str {s}"
          | .bool b => s!"bool {b}"
        let (b, id) := mkNode b tag (effectsFn b.env e)
        pure (b, id, #[id])
    | .block ss =>
        let (b, entry?, exits) ← buildStmts effectsFn ctx? b ss
        match entry? with
        | some e => pure (b, e, exits)
        | none =>
            let (b, id) := mkNode b "empty" #[]
            pure (b, id, #[id])
    | .if_ cond thenStmts =>
        let (b, condId) := mkNode b "if" (effectsFn b.env cond)
        let env0 := b.env
        let (b, thenEntry?, thenExits) ← buildStmts effectsFn ctx? b thenStmts
        let b := { b with env := env0 }
        let (b, joinId) := mkNode b "join" #[]
        let thenEntry :=
          match thenEntry? with
          | some e => e
          | none => joinId
        -- Cond jumps to then (if any) or to join (skip).
        let succs := if thenEntry = joinId then #[joinId] else #[thenEntry, joinId]
        let b := setSuccs b condId succs
        -- Then exits fall through to join.
        let b := connectExits b thenExits joinId
        pure (b, condId, #[joinId])
    | .switch_ scrut cases def? =>
        let (b, scrutId) := mkNode b "switch" (effectsFn b.env scrut)
        let (b, joinId) := mkNode b "join" #[]
        let env0 := b.env
        let rec buildCases (i : Nat) (b : Builder) (succs : Array NodeId) :
            Except String (Builder × Array NodeId) := do
          if i < cases.size then
            let ss := (cases[i]!).2
            let (b, entry?, exits) ← buildStmts effectsFn ctx? b ss
            let b := { b with env := env0 }
            let entry := entry?.getD joinId
            let b := connectExits b exits joinId
            buildCases (i + 1) b (succs.push entry)
          else
            pure (b, succs)
        let (b, succs) ← buildCases 0 b #[]
        let (b, succs) ←
          match def? with
          | none => pure (b, succs.push joinId)
          | some ss =>
              let (b, entry?, exits) ← buildStmts effectsFn ctx? b ss
              let b := { b with env := env0 }
              let entry := entry?.getD joinId
              let b := connectExits b exits joinId
              pure (b, succs.push entry)
        let b := setSuccs b scrutId (sortDedupNat (succs.push joinId))
        pure (b, scrutId, #[joinId])
    | .for_ init cond post body =>
        let (b, initEntry?, initExits) ← buildStmts effectsFn ctx? b init
        let (b, condId) := mkNode b "for.cond" (effectsFn b.env cond)
        let (b, joinId) := mkNode b "for.join" #[]

        -- Post runs after each body iteration; `continue` should jump to post (if any), else to cond.
        let postCtx : LoopCtx := { breakTarget := joinId, continueTarget := condId }
        let (b, postEntry?, postExits) ← buildStmts effectsFn (some postCtx) b post
        let postEntry := postEntry?.getD condId

        let bodyCtx : LoopCtx := { breakTarget := joinId, continueTarget := postEntry }
        let (b, bodyEntry?, bodyExits) ← buildStmts effectsFn (some bodyCtx) b body
        let bodyEntry := bodyEntry?.getD postEntry

        let mut b := b
        -- init -> cond
        b := connectExits b initExits condId
        -- cond -> body or join
        b := setSuccs b condId #[bodyEntry, joinId]
        -- body -> post
        b := connectExits b bodyExits postEntry
        -- post -> cond (back-edge)
        b := connectExits b postExits condId

        let entry := initEntry?.getD condId
        pure (b, entry, #[joinId])
    | .break =>
        let (b, id) := mkNode b "break" #[]
        match ctx? with
        | none => pure (b, id, #[])
        | some ctx =>
            let b := setSuccs b id #[ctx.breakTarget]
            pure (b, id, #[])
    | .continue =>
        let (b, id) := mkNode b "continue" #[]
        match ctx? with
        | none => pure (b, id, #[])
        | some ctx =>
            let b := setSuccs b id #[ctx.continueTarget]
            pure (b, id, #[])
    | .return_ args =>
        let effs :=
          args.foldl (fun acc a => acc ++ effectsFn b.env a) #[]
        let (b, id) := mkNode b "return" effs
        pure (b, id, #[])
    | .revert args =>
        let effs :=
          args.foldl (fun acc a => acc ++ effectsFn b.env a) #[]
        let (b, id) := mkNode b "revert" effs
        pure (b, id, #[])
    | .leave =>
        let (b, id) := mkNode b "leave" #[]
        pure (b, id, #[])
end

def toAlgebraIRWithEffects (body : Array Stmt) (effectsFn : EffectsFn) : Graph :=
  let b0 : Builder := {}
  let (b, entry?, _) :=
    match (buildStmts effectsFn none b0 body) with
    | .ok r => r
    | .error _ =>
        -- Parsing succeeded, but CFG construction shouldn't fail in this subset.
        -- Fall back to an empty graph.
        (b0, none, #[])
  let (b, entry) :=
    match entry? with
    | some e => (b, e)
    | none =>
        let (b, id) := mkNode b "empty" #[]
        (b, id)
  let exits :=
    b.nodes.foldl (fun acc n => if n.succs.isEmpty then acc.push n.id else acc) #[]
  { entry := entry, exits := exits, nodes := b.nodes }

def toAlgebraIR (body : Array Stmt) : Graph :=
  toAlgebraIRWithEffects body effectsOfExpr

end HeytingLean.BountyHunter.Solc.YulTextMini
