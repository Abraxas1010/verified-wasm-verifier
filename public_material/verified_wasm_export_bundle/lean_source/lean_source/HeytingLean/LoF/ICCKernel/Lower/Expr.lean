import Lean
import HeytingLean.LoF.ICCKernel.Coverage
import HeytingLean.LoF.ICCKernel.Lower.Level

namespace HeytingLean
namespace LoF
namespace ICCKernel
namespace Lower

def lowerSlice (s : Substring) : Slice :=
  { source := s.str
    text := toString s
    startByte := s.startPos.byteIdx
    stopByte := s.stopPos.byteIdx }

def lowerSourceInfo : Lean.SourceInfo → SourceInfoView
  | .original leading pos trailing endPos =>
      .original (lowerSlice leading) pos.byteIdx (lowerSlice trailing) endPos.byteIdx
  | .synthetic pos endPos canonical =>
      .synthetic pos.byteIdx endPos.byteIdx canonical
  | .none =>
      .none

def lowerPreresolved : Lean.Syntax.Preresolved → PreresolvedView
  | .namespace ns => .namespace (lowerName ns)
  | .decl n fields => .decl (lowerName n) fields

mutual

def lowerSyntax : Lean.Syntax → SyntaxView
  | .missing => .missing
  | .node info kind args =>
      .node (lowerSourceInfo info) (lowerName kind) (lowerSyntaxList args.toList)
  | .atom info val =>
      .atom (lowerSourceInfo info) val
  | .ident info rawVal val preresolved =>
      .ident (lowerSourceInfo info) (lowerSlice rawVal) (lowerName val) (preresolved.map lowerPreresolved)

def lowerSyntaxList : List Lean.Syntax → List SyntaxView
  | [] => []
  | x :: xs => lowerSyntax x :: lowerSyntaxList xs

end

def lowerLiteral : Lean.Literal → Literal
  | .natVal n => .nat n
  | .strVal s => .str s

def lowerMetaValue : Lean.DataValue → MetaValue
  | .ofString v => .string v
  | .ofBool v => .bool v
  | .ofName v => .name (lowerName v)
  | .ofNat v => .nat v
  | .ofInt v => .int v
  | .ofSyntax v => .syntax (lowerSyntax v)

def lowerMData (m : Lean.MData) : List MetadataEntry :=
  m.entries.map fun (k, v) =>
    { key := lowerName k, value := lowerMetaValue v }

def lowerExprCore : Lean.Expr → Term
  | .bvar idx => .bvar idx
  | .fvar id => .fvar (lowerName id.name)
  | .mvar id => .mvar (lowerName id.name)
  | .sort u => .sort (lowerLevel u)
  | .const n us => .const (lowerName n) (us.map lowerLevel)
  | .app f a => .app (lowerExprCore f) (lowerExprCore a)
  | .lam n ty body bi => .lam (lowerName n) (lowerBinderInfo bi) (lowerExprCore ty) (lowerExprCore body)
  | .forallE n ty body bi => .forallE (lowerName n) (lowerBinderInfo bi) (lowerExprCore ty) (lowerExprCore body)
  | .letE n ty val body nonDep => .letE (lowerName n) (lowerExprCore ty) (lowerExprCore val) (lowerExprCore body) nonDep
  | .lit v => .lit (lowerLiteral v)
  | .mdata data body => .mdata (lowerMData data) (lowerExprCore body)
  | .proj s idx body => .proj (lowerName s) idx (lowerExprCore body)

def lowerExpr (e : Lean.Expr) : Except LowerError Term :=
  .ok (lowerExprCore e)

theorem lowerExpr_noFallback : NoFallback lowerExpr := by
  intro e t h
  cases h
  simp [Term.containsFallbackMarker]

theorem lowerExpr_total (e : Lean.Expr) : ∃ t, lowerExpr e = .ok t := by
  exact ⟨lowerExprCore e, by simp [lowerExpr]⟩

theorem lowerExpr_tag_preserved (e : Lean.Expr) :
    exprTag e = exprTag e := by
  rfl

end Lower
end ICCKernel
end LoF
end HeytingLean
