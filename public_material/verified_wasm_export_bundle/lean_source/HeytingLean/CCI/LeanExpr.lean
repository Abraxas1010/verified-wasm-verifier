import Lean
import HeytingLean.CCI.Core

/-!
# CCI LeanExpr Bridge

Lower core Lean syntax into the richer CCI carrier. This is a structural bridge:
it preserves enough syntax to transport declarations honestly, but it does not
claim that the lightweight CCI checker re-validates Lean kernel semantics.
-/

open Lean

namespace HeytingLean
namespace CCI

def ofBinderInfo : Lean.BinderInfo → BinderStyle
  | .default => .default
  | .implicit => .implicit
  | .strictImplicit => .strictImplicit
  | .instImplicit => .instImplicit

def ofLevel : Lean.Level → ULevel
  | .zero => .zero
  | .succ u => .succ (ofLevel u)
  | .max u v => .max (ofLevel u) (ofLevel v)
  | .imax u v => .imax (ofLevel u) (ofLevel v)
  | .param n => .param n.toString
  | .mvar id => .mvar id.name.toString

def ofLiteral : Lean.Literal → LitVal
  | .natVal n => .nat n
  | .strVal s => .str s

def ofExpr : Lean.Expr → Expr
  | .bvar idx => .bvar idx
  | .sort u => .sort (ofLevel u)
  | .const n us => .const n.toString (us.map ofLevel)
  | .app f a => .app (ofExpr f) (ofExpr a)
  | .lam n ty body bi => .lam n.toString (ofBinderInfo bi) (ofExpr ty) (ofExpr body)
  | .forallE n ty body bi => .forallE n.toString (ofBinderInfo bi) (ofExpr ty) (ofExpr body)
  | .letE n ty val body _ => .letE n.toString (ofExpr ty) (ofExpr val) (ofExpr body)
  | .lit v => .lit (ofLiteral v)
  | .mdata _ body => ofExpr body
  | .proj s idx body => .proj s.toString idx (ofExpr body)
  | .fvar id => .fvar id.name.toString
  | .mvar id => .mvar id.name.toString

end CCI
end HeytingLean
