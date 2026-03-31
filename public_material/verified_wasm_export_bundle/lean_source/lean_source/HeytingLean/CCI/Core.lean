import Lean.Data.Json

/-!
# CCI Core — minimal canonical IR (v1)

Closed, nucleus‑passed expressions and opaque lens payloads for export/check.
The propositional fragment remains intentionally small and opinionated to keep
the checker trivial, but the carrier also needs enough syntax to faithfully
transport richer Lean expressions across the repo.
-/

namespace HeytingLean
namespace CCI

abbrev Digest := ByteArray
abbrev AtomId := String

inductive ULevel
  | zero
  | succ (u : ULevel)
  | max (a b : ULevel)
  | imax (a b : ULevel)
  | param (name : String)
  | mvar (name : String)
  deriving Repr, DecidableEq

inductive BinderStyle
  | default
  | implicit
  | strictImplicit
  | instImplicit
  deriving Repr, DecidableEq

inductive LitVal
  | nat (value : Nat)
  | str (value : String)
  deriving Repr, DecidableEq

inductive Expr
  | atom (id : AtomId)
  | andR (a b : Expr)
  | orR  (a b : Expr)
  | impR (a b : Expr)
  | notR (a : Expr)
  | bvar (idx : Nat)
  | sort (level : ULevel)
  | const (name : String) (levels : List ULevel)
  | app (fn arg : Expr)
  | lam (binder : String) (binderInfo : BinderStyle) (type body : Expr)
  | forallE (binder : String) (binderInfo : BinderStyle) (type body : Expr)
  | letE (binder : String) (type value body : Expr)
  | lit (value : LitVal)
  | proj (structName : String) (idx : Nat) (expr : Expr)
  | fvar (name : String)
  | mvar (name : String)
  deriving Repr, DecidableEq

def top : Expr := .atom "⊤"
def bot : Expr := .atom "⊥"

def ULevel.structuralKey : ULevel → String
  | .zero => "zero"
  | .succ u => "succ(" ++ structuralKey u ++ ")"
  | .max a b => "max(" ++ structuralKey a ++ "," ++ structuralKey b ++ ")"
  | .imax a b => "imax(" ++ structuralKey a ++ "," ++ structuralKey b ++ ")"
  | .param n => "param(" ++ n ++ ")"
  | .mvar n => "mvar(" ++ n ++ ")"

def BinderStyle.structuralKey : BinderStyle → String
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

def LitVal.structuralKey : LitVal → String
  | .nat n => "nat(" ++ toString n ++ ")"
  | .str s => "str(" ++ s ++ ")"

def Expr.structuralKey : Expr → String
  | .atom id => "A:" ++ id
  | .andR a b => "&(" ++ structuralKey a ++ "," ++ structuralKey b ++ ")"
  | .orR a b => "|(" ++ structuralKey a ++ "," ++ structuralKey b ++ ")"
  | .impR a b => ">(" ++ structuralKey a ++ "," ++ structuralKey b ++ ")"
  | .notR a => "~(" ++ structuralKey a ++ ")"
  | .bvar idx => "bvar(" ++ toString idx ++ ")"
  | .sort u => "sort(" ++ u.structuralKey ++ ")"
  | .const n us =>
      "const(" ++ n ++ ";[" ++ String.intercalate "," (us.map ULevel.structuralKey) ++ "])"
  | .app f a => "app(" ++ structuralKey f ++ "," ++ structuralKey a ++ ")"
  | .lam n bi ty body =>
      "lam(" ++ n ++ ";" ++ bi.structuralKey ++ ";" ++ structuralKey ty ++ ";" ++ structuralKey body ++ ")"
  | .forallE n bi ty body =>
      "forall(" ++ n ++ ";" ++ bi.structuralKey ++ ";" ++ structuralKey ty ++ ";" ++ structuralKey body ++ ")"
  | .letE n ty val body =>
      "let(" ++ n ++ ";" ++ structuralKey ty ++ ";" ++ structuralKey val ++ ";" ++ structuralKey body ++ ")"
  | .lit v => "lit(" ++ v.structuralKey ++ ")"
  | .proj s idx e => "proj(" ++ s ++ ";" ++ toString idx ++ ";" ++ structuralKey e ++ ")"
  | .fvar n => "fvar(" ++ n ++ ")"
  | .mvar n => "mvar(" ++ n ++ ")"

structure Lens where
  name  : String
  value : String   -- opaque payload (e.g., JSON-serialized elsewhere)
  deriving Repr, DecidableEq

end CCI
end HeytingLean
