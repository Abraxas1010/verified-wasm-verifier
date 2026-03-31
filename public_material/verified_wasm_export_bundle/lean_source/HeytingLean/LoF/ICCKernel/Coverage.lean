import Lean
import Lean.Data.Json
import HeytingLean.LoF.ICCKernel.Env
import HeytingLean.LoF.ICCKernel.Semantics

/-!
# ICCKernel.Coverage

Executable support/coverage surface for the direct Lean-to-ICCKernel lowering.
-/

namespace HeytingLean
namespace LoF
namespace ICCKernel

inductive ExprTag where
  | bvar
  | fvar
  | mvar
  | sort
  | const
  | app
  | lam
  | forallE
  | letE
  | lit
  | mdata
  | proj
  deriving Repr, Inhabited, Lean.ToJson

def ExprTag.tag : ExprTag → String
  | .bvar => "bvar"
  | .fvar => "fvar"
  | .mvar => "mvar"
  | .sort => "sort"
  | .const => "const"
  | .app => "app"
  | .lam => "lam"
  | .forallE => "forallE"
  | .letE => "letE"
  | .lit => "lit"
  | .mdata => "mdata"
  | .proj => "proj"

def exprTag : Lean.Expr → ExprTag
  | .bvar _ => .bvar
  | .fvar _ => .fvar
  | .mvar _ => .mvar
  | .sort _ => .sort
  | .const _ _ => .const
  | .app _ _ => .app
  | .lam .. => .lam
  | .forallE .. => .forallE
  | .letE .. => .letE
  | .lit _ => .lit
  | .mdata _ _ => .mdata
  | .proj .. => .proj

inductive LowerErrorKind where
  | unsupportedExpr
  | unsupportedConstant
  | invalidInput
  deriving Repr, Inhabited, Lean.ToJson

structure LowerError where
  kind : LowerErrorKind
  message : String
  provenance : String := ""
  deriving Repr, Inhabited, Lean.ToJson

def NoFallback (f : Lean.Expr → Except LowerError Term) : Prop :=
  ∀ e t, f e = .ok t → Term.containsFallbackMarker t = false

def NoConstantFallback (f : Lean.ConstantInfo → Except LowerError ConstantInfo) : Prop :=
  ∀ c t, f c = .ok t →
    match t.valueTerm? with
    | none => True
    | some v => Term.containsFallbackMarker v = false

def SupportedExpr : Lean.Expr → Prop
  | .bvar _ => True
  | .fvar _ => True
  | .mvar _ => True
  | .sort _ => True
  | .const _ _ => True
  | .app f a => SupportedExpr f ∧ SupportedExpr a
  | .lam _ ty body _ => SupportedExpr ty ∧ SupportedExpr body
  | .forallE _ ty body _ => SupportedExpr ty ∧ SupportedExpr body
  | .letE _ ty val body _ => SupportedExpr ty ∧ SupportedExpr val ∧ SupportedExpr body
  | .lit _ => True
  | .mdata _ body => SupportedExpr body
  | .proj _ _ body => SupportedExpr body

def SupportedRecursorRule (r : Lean.RecursorRule) : Prop :=
  SupportedExpr r.rhs

def SupportedConstantInfo : Lean.ConstantInfo → Prop
  | .axiomInfo v => SupportedExpr v.type
  | .defnInfo v => SupportedExpr v.type ∧ SupportedExpr v.value
  | .thmInfo v => SupportedExpr v.type ∧ SupportedExpr v.value
  | .opaqueInfo v => SupportedExpr v.type ∧ SupportedExpr v.value
  | .quotInfo v => SupportedExpr v.type
  | .inductInfo v => SupportedExpr v.type
  | .ctorInfo v => SupportedExpr v.type
  | .recInfo v => SupportedExpr v.type ∧ ∀ r ∈ v.rules, SupportedRecursorRule r

theorem supportedExpr_all : ∀ e : Lean.Expr, SupportedExpr e
  | .bvar _ => by trivial
  | .fvar _ => by trivial
  | .mvar _ => by trivial
  | .sort _ => by trivial
  | .const _ _ => by trivial
  | .app f a => by exact ⟨supportedExpr_all f, supportedExpr_all a⟩
  | .lam _ ty body _ => by exact ⟨supportedExpr_all ty, supportedExpr_all body⟩
  | .forallE _ ty body _ => by exact ⟨supportedExpr_all ty, supportedExpr_all body⟩
  | .letE _ ty val body _ => by
      exact ⟨supportedExpr_all ty, supportedExpr_all val, supportedExpr_all body⟩
  | .lit _ => by trivial
  | .mdata _ body => by exact supportedExpr_all body
  | .proj _ _ body => by exact supportedExpr_all body

theorem supportedConstantInfo_all (c : Lean.ConstantInfo) : SupportedConstantInfo c := by
  cases c with
  | axiomInfo v =>
      exact supportedExpr_all v.type
  | defnInfo v =>
      exact ⟨supportedExpr_all v.type, supportedExpr_all v.value⟩
  | thmInfo v =>
      exact ⟨supportedExpr_all v.type, supportedExpr_all v.value⟩
  | opaqueInfo v =>
      exact ⟨supportedExpr_all v.type, supportedExpr_all v.value⟩
  | quotInfo v =>
      exact supportedExpr_all v.type
  | inductInfo v =>
      exact supportedExpr_all v.type
  | ctorInfo v =>
      exact supportedExpr_all v.type
  | recInfo v =>
      refine ⟨supportedExpr_all v.type, ?_⟩
      intro r hr
      exact supportedExpr_all r.rhs

end ICCKernel
end LoF
end HeytingLean
