import Std
import HeytingLean.BountyHunter.Solc.YulTextMini.Types

/-!
# HeytingLean.BountyHunter.Solc.YulTextMini.AlphaRename

Deterministic alpha-renaming for YulTextMini statement ASTs.

Purpose: create a semantics-preserving (name-only) transformation so we can validate
“AlgebraIR2 → codegen” against the strict parity oracle *without* borrowing
identifier choices from solc’s IR.

Notes:
- This does **not** rename function names (call heads). Only bound variables / identifiers.
- Scoping is approximated by treating blocks/branches as nested scopes.
- If solc uses shadowing, this should still be handled (new scope gets fresh names).
-/

namespace HeytingLean.BountyHunter.Solc.YulTextMini

abbrev NameMap := Std.HashMap String String

structure RenameState where
  nextId : Nat := 0
  scopes : List NameMap := [Std.HashMap.emptyWithCapacity 64]
  deriving Inhabited

private def fresh (st : RenameState) : (RenameState × String) :=
  let name := s!"v{st.nextId}"
  ({ st with nextId := st.nextId + 1 }, name)

private def pushScope (st : RenameState) : RenameState :=
  { st with scopes := (Std.HashMap.emptyWithCapacity 32) :: st.scopes }

private def popScope (st : RenameState) : RenameState :=
  match st.scopes with
  | [] => st
  | _ :: rest =>
      -- Keep at least one scope.
      match rest with
      | [] => st
      | _ => { st with scopes := rest }

private def lookup? (st : RenameState) (k : String) : Option String :=
  st.scopes.findSome? (fun m => m.get? k)

private def bind (st : RenameState) (k v : String) : RenameState :=
  match st.scopes with
  | [] => st
  | top :: rest => { st with scopes := (top.insert k v) :: rest }

private partial def renameExpr (st : RenameState) : Expr → Expr
  | .ident name =>
      match lookup? st name with
      | some v => .ident v
      | none => .ident name
  | .nat n => .nat n
  | .str s => .str s
  | .bool b => .bool b
  | .call fn args =>
      .call fn (args.map (renameExpr st))

private partial def renameBinders (st : RenameState) (names : Array String) : (RenameState × Array String) :=
  Id.run do
    let mut st := st
    let mut out : Array String := #[]
    for n in names do
      let (st2, v) := fresh st
      st := bind st2 n v
      out := out.push v
    return (st, out)

mutual
  private partial def renameStmt (st : RenameState) (s : Stmt) : (RenameState × Stmt) :=
    match s with
    | .let_ name rhs =>
        let rhs' := renameExpr st rhs
        let (st2, v) := fresh st
        let st2 := bind st2 name v
        (st2, .let_ v rhs')
    | .letMany names rhs =>
        let rhs' := renameExpr st rhs
        let (st2, vs) := renameBinders st names
        (st2, .letMany vs rhs')
    | .assign name rhs =>
        let rhs' := renameExpr st rhs
        match lookup? st name with
        | some v => (st, .assign v rhs')
        | none =>
            -- Likely a function parameter or return variable (declared in the function header).
            -- We do not rename it unless we also rename the header.
            (st, .assign name rhs')
    | .assignMany names rhs =>
        let rhs' := renameExpr st rhs
        let (st2, out) :=
          names.foldl
            (init := (st, (#[] : Array String)))
            (fun (acc : RenameState × Array String) n =>
              let stAcc := acc.1
              let outAcc := acc.2
              match lookup? stAcc n with
              | some v => (stAcc, outAcc.push v)
              | none => (stAcc, outAcc.push n))
        (st2, .assignMany out rhs')
    | .expr e =>
        (st, .expr (renameExpr st e))
    | .return_ args =>
        (st, .return_ (args.map (renameExpr st)))
    | .revert args =>
        (st, .revert (args.map (renameExpr st)))
    | .break => (st, .break)
    | .continue => (st, .continue)
    | .leave => (st, .leave)
    | .block ss =>
        let stIn := pushScope st
        let (stOut, ss') := renameStmts stIn ss
        (popScope stOut, .block ss')
    | .if_ cond thenStmts =>
        let cond' := renameExpr st cond
        let stIn := pushScope st
        let (stOut, ss') := renameStmts stIn thenStmts
        (popScope stOut, .if_ cond' ss')
    | .switch_ scrut cases def? =>
        let scrut' := renameExpr st scrut
        let (stAcc, casesOut) :=
          cases.foldl
            (init := (st, (#[] : Array (Lit × Array Stmt))))
            (fun (acc : RenameState × Array (Lit × Array Stmt)) c =>
              let stAcc := acc.1
              let casesAcc := acc.2
              let stIn := pushScope stAcc
              let (stOut, body') := renameStmts stIn c.2
              let stAcc := popScope stOut
              (stAcc, casesAcc.push (c.1, body')))
        let (stAcc, defOut?) :=
          match def? with
          | none => (stAcc, none)
          | some body =>
              let stIn := pushScope stAcc
              let (stOut, body') := renameStmts stIn body
              (popScope stOut, some body')
        (stAcc, .switch_ scrut' casesOut defOut?)
    | .for_ init cond post body =>
        -- Yul syntax uses `{ init } cond { post } { body }` with block scopes.
        let stIn := pushScope st
        let (st1, init') := renameStmts stIn init
        let cond' := renameExpr st1 cond
        let (st2, post') := renameStmts (pushScope st1) post
        let st2 := popScope st2
        let (st3, body') := renameStmts (pushScope st2) body
        let st3 := popScope st3
        (popScope st3, .for_ init' cond' post' body')

  private partial def renameStmts (st : RenameState) (ss : Array Stmt) : (RenameState × Array Stmt) :=
    Id.run do
      let mut st := st
      let mut out : Array Stmt := #[]
      for s in ss do
        let (st2, s') := renameStmt st s
        st := st2
        out := out.push s'
      return (st, out)
end

def alphaRename (ss : Array Stmt) : Array Stmt :=
  (renameStmts {} ss).2

end HeytingLean.BountyHunter.Solc.YulTextMini
