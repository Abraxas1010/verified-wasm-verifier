import HeytingLean.BountyHunter.YulMini.Types

/-!
# HeytingLean.BountyHunter.YulMini.Examples

Canonical YulMini programs capturing the EtherStore CEI pattern.
-/

namespace HeytingLean.BountyHunter.YulMini

private def b (bi : Builtin) (args : Array Expr := #[]) : Expr :=
  Expr.builtin bi args

private def v (x : Ident) : Expr :=
  Expr.var x

private def n (k : Nat) : Expr :=
  Expr.nat k

/-- Vulnerable withdraw: external call occurs before storage write. -/
def etherStoreVuln : Program :=
  { funcs := #[
      { name := "withdraw"
        body := #[
          Stmt.let_ "bal" (b (.sload 0) #[])
        , Stmt.if_ (v "cond") #[] #[Stmt.revert]      -- guard; else branch reverts
        , Stmt.expr (b (.call "attacker") #[v "bal"])
        , Stmt.expr (b (.sstore 0) #[n 0])
        , Stmt.return_
        ]
      }
    ] }

/-- Fixed withdraw: storage write occurs before external call. -/
def etherStoreFixed : Program :=
  { funcs := #[
      { name := "withdraw"
        body := #[
          Stmt.let_ "bal" (b (.sload 0) #[])
        , Stmt.if_ (v "cond") #[] #[Stmt.revert]
        , Stmt.expr (b (.sstore 0) #[n 0])
        , Stmt.expr (b (.call "attacker") #[v "bal"])
        , Stmt.return_
        ]
      }
    ] }

end HeytingLean.BountyHunter.YulMini
