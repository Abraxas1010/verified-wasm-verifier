import Std
import HeytingLean.BountyHunter.Solc.YulTextMini.Types

/-!
# HeytingLean.BountyHunter.AlgebraIR2.ANF

Deterministic A-normalization pass for `YulTextMini` statement bodies.

Purpose (chokepoint-driven):
- make the AlgebraIR2 codegen path less “structure-borrowing” from solc’s IR
  text by performing a semantics-preserving, name-only/value-structure rewrite
  *after* parsing and alpha-renaming.
- keep it conservative: do not attempt full Yul correctness; only normalize
  what we can do without changing evaluation frequency in loops.

Current behavior:
- Flattens nested call arguments by introducing fresh `let`-bound temporaries.
- Hoists temporaries in contexts where the expression is evaluated once
  (`let/assign/expr/if/switch/return/revert`).
- Leaves `for` loop conditions untouched (no hoisting across iterations).
- Fresh names are generated deterministically and avoid collisions.
-/

namespace HeytingLean.BountyHunter.AlgebraIR2

open HeytingLean.BountyHunter.Solc
open YulTextMini

private structure AnfState where
  nextId : Nat := 0
  used : Std.HashSet String := {}

private abbrev AnfM := ExceptT String (StateM AnfState)

private def isAtom : Expr → Bool
  | .ident _ => true
  | .nat _ => true
  | .str _ => true
  | .bool _ => true
  | .call _ _ => false

private def collectExprNames (e : Expr) (acc : Std.HashSet String) : Std.HashSet String :=
  match e with
  | .ident s => acc.insert s
  | .nat _ => acc
  | .str _ => acc
  | .bool _ => acc
  | .call _ args =>
      args.foldl (fun a x => collectExprNames x a) acc

private partial def collectStmtNames (s : Stmt) (acc : Std.HashSet String) : Std.HashSet String :=
  match s with
  | .let_ n rhs => collectExprNames rhs (acc.insert n)
  | .letMany ns rhs =>
      let acc := ns.foldl (fun a x => a.insert x) acc
      collectExprNames rhs acc
  | .assign n rhs => collectExprNames rhs (acc.insert n)
  | .assignMany ns rhs =>
      let acc := ns.foldl (fun a x => a.insert x) acc
      collectExprNames rhs acc
  | .expr e => collectExprNames e acc
  | .if_ c t =>
      let acc := collectExprNames c acc
      t.foldl (fun a x => collectStmtNames x a) acc
  | .switch_ s cases def? =>
      let acc := collectExprNames s acc
      let acc := cases.foldl (fun a p => p.2.foldl (fun a2 x => collectStmtNames x a2) a) acc
      match def? with
      | none => acc
      | some d => d.foldl (fun a x => collectStmtNames x a) acc
  | .for_ init cond post body =>
      let acc := init.foldl (fun a x => collectStmtNames x a) acc
      let acc := collectExprNames cond acc
      let acc := post.foldl (fun a x => collectStmtNames x a) acc
      body.foldl (fun a x => collectStmtNames x a) acc
  | .break => acc
  | .continue => acc
  | .block ss => ss.foldl (fun a x => collectStmtNames x a) acc
  | .return_ args => args.foldl (fun a x => collectExprNames x a) acc
  | .revert args => args.foldl (fun a x => collectExprNames x a) acc
  | .leave => acc

private def initialUsedNames (ss : Array Stmt) : Std.HashSet String :=
  ss.foldl (fun a s => collectStmtNames s a) {}

private def freshName : AnfM String := do
  let st ← get
  let (n, nm) := Id.run do
    let mut n := st.nextId
    let mut nm := s!"__bh_anf${n}"
    while st.used.contains nm do
      n := n + 1
      nm := s!"__bh_anf${n}"
    return (n, nm)
  set { st with nextId := n + 1, used := st.used.insert nm }
  pure nm

private def anfExprNoHoist (e : Expr) : Expr :=
  -- Normalize “in place” without introducing new lets.
  match e with
  | .ident _ => e
  | .nat _ => e
  | .str _ => e
  | .bool _ => e
  | .call fn args => .call fn (args.map anfExprNoHoist)

mutual
  private partial def anfExprE (e : Expr) : AnfM (Array Stmt × Expr) := do
    match e with
    | .ident _ => pure (#[], e)
    | .nat _ => pure (#[], e)
    | .str _ => pure (#[], e)
    | .bool _ => pure (#[], e)
    | .call fn args => do
        let acc ← args.foldlM
          (init := ((#[] : Array Stmt), (#[] : Array Expr)))
          (fun (acc : Array Stmt × Array Expr) a => do
            let (p, atom) ← anfExprAtomE a
            pure (acc.1 ++ p, acc.2.push atom))
        pure (acc.1, .call fn acc.2)

  private partial def anfExprAtomE (e : Expr) : AnfM (Array Stmt × Expr) := do
    if isAtom e then
      pure (#[], e)
    else do
      let (p, e') ← anfExprE e
      let nm ← freshName
      let p := p.push (.let_ nm e')
      pure (p, .ident nm)
end

private def anfArgsE (args : Array Expr) : AnfM (Array Stmt × Array Expr) := do
  args.foldlM (init := ((#[] : Array Stmt), (#[] : Array Expr))) (fun (acc : Array Stmt × Array Expr) a => do
    let (p, e') ← anfExprE a
    pure (acc.1 ++ p, acc.2.push e'))

mutual
  private partial def anfStmtE (s : Stmt) : AnfM (Array Stmt) := do
    match s with
    | .let_ name rhs =>
        let (p, rhs') ← anfExprE rhs
        pure (p.push (.let_ name rhs'))
    | .letMany names rhs =>
        let (p, rhs') ← anfExprE rhs
        pure (p.push (.letMany names rhs'))
    | .assign name rhs =>
        let (p, rhs') ← anfExprE rhs
        pure (p.push (.assign name rhs'))
    | .assignMany names rhs =>
        let (p, rhs') ← anfExprE rhs
        pure (p.push (.assignMany names rhs'))
    | .expr e =>
        let (p, e') ← anfExprE e
        pure (p.push (.expr e'))
    | .if_ cond thenStmts =>
        let (p, condAtom) ← anfExprAtomE cond
        let thenStmts' ← anfStmtsE thenStmts
        pure (p.push (.if_ condAtom thenStmts'))
    | .switch_ scrut cases def? =>
        let (p, scrutAtom) ← anfExprAtomE scrut
        let cases' ←
          cases.foldlM (init := (#[] : Array (Lit × Array Stmt))) (fun (acc : Array (Lit × Array Stmt)) (it : Lit × Array Stmt) => do
            let body' ← anfStmtsE it.2
            pure (acc.push (it.1, body')))
        let def?' ←
          match def? with
          | none => pure none
          | some body => some <$> anfStmtsE body
        pure (p.push (.switch_ scrutAtom cases' def?'))
    | .for_ init cond post body =>
        -- Do not hoist temporaries into the loop condition (changes evaluation frequency).
        let init' ← anfStmtsE init
        let post' ← anfStmtsE post
        let body' ← anfStmtsE body
        pure #[.for_ init' (anfExprNoHoist cond) post' body']
    | .break => pure #[.break]
    | .continue => pure #[.continue]
    | .block ss =>
        let ss' ← anfStmtsE ss
        pure #[.block ss']
    | .return_ args =>
        let (p, args') ← anfArgsE args
        pure (p.push (.return_ args'))
    | .revert args =>
        let (p, args') ← anfArgsE args
        pure (p.push (.revert args'))
    | .leave => pure #[.leave]

  private partial def anfStmtsE (ss : Array Stmt) : AnfM (Array Stmt) := do
    ss.foldlM (init := (#[] : Array Stmt)) (fun (acc : Array Stmt) s => do
      let ss' ← anfStmtE s
      pure (acc ++ ss'))
end

def anfStmts (ss : Array Stmt) : Except String (Array Stmt) := do
  let used := initialUsedNames ss
  let (out, _st) := (anfStmtsE ss).run { used := used } |>.run
  out

end HeytingLean.BountyHunter.AlgebraIR2
