import Lean
import HeytingLean.LoF.ICCKernel.Lower.Expr
import HeytingLean.LoF.ICCKernel.Raise.Level

namespace HeytingLean
namespace LoF
namespace ICCKernel
namespace Raise

def raiseSlice (s : Slice) : Substring :=
  { str := s.source
    startPos := ⟨s.startByte⟩
    stopPos := ⟨s.stopByte⟩ }

def raiseSourceInfo : SourceInfoView → Lean.SourceInfo
  | .original leading posByte trailing endPosByte =>
      .original (raiseSlice leading) ⟨posByte⟩ (raiseSlice trailing) ⟨endPosByte⟩
  | .synthetic posByte endPosByte canonical =>
      .synthetic ⟨posByte⟩ ⟨endPosByte⟩ canonical
  | .none =>
      .none

def raisePreresolved : PreresolvedView → Lean.Syntax.Preresolved
  | .namespace ns => .namespace (raiseName ns)
  | .decl name fields => .decl (raiseName name) fields

def raiseSyntax : SyntaxView → Lean.Syntax
  | .missing =>
      .missing
  | .node info kind args =>
      .node (raiseSourceInfo info) (raiseName kind) (args.map raiseSyntax).toArray
  | .atom info val =>
      .atom (raiseSourceInfo info) val
  | .ident info rawVal val preresolved =>
      .ident (raiseSourceInfo info) (raiseSlice rawVal) (raiseName val) (preresolved.map raisePreresolved)

def raiseMetaValue : MetaValue → Lean.DataValue
  | .string s => .ofString s
  | .bool b => .ofBool b
  | .name n => .ofName (raiseName n)
  | .nat n => .ofNat n
  | .int n => .ofInt n
  | .syntax stx => .ofSyntax (raiseSyntax stx)

theorem raiseLiteral_lowerLiteral (lit : Lean.Literal) :
    raiseLiteral (Lower.lowerLiteral lit) = lit := by
  cases lit <;> rfl

def raiseMData (entries : List MetadataEntry) : Lean.MData :=
  { entries := entries.map fun
      | ⟨key, value⟩ => (raiseName key, raiseMetaValue value) }

def raiseTerm : Term → Except LowerError Lean.Expr
  | .bvar idx => .ok (.bvar idx)
  | .fvar name => .ok (.fvar (.mk (raiseName name)))
  | .mvar name => .ok (.mvar (.mk (raiseName name)))
  | .sort level => .ok (.sort (raiseLevel level))
  | .const name levels => .ok (.const (raiseName name) (levels.map raiseLevel))
  | .app fn arg => do
      return .app (← raiseTerm fn) (← raiseTerm arg)
  | .lam binder binderInfo type body => do
      return .lam (raiseName binder) (← raiseTerm type) (← raiseTerm body) (raiseBinderInfo binderInfo)
  | .forallE binder binderInfo type body => do
      return .forallE (raiseName binder) (← raiseTerm type) (← raiseTerm body) (raiseBinderInfo binderInfo)
  | .letE binder type value body nonDep => do
      return .letE (raiseName binder) (← raiseTerm type) (← raiseTerm value) (← raiseTerm body) nonDep
  | .lit value =>
      .ok (.lit (raiseLiteral value))
  | .mdata entries body => do
      return .mdata (raiseMData entries) (← raiseTerm body)
  | .proj structName idx expr => do
      return .proj (raiseName structName) idx (← raiseTerm expr)
  | .bridge _ =>
      .error { kind := .unsupportedExpr, message := "bridge is not in the Lean.Expr source image", provenance := "ICCKernel.Raise.raiseTerm" }
  | .ann _ _ =>
      .error { kind := .unsupportedExpr, message := "ann is not in the Lean.Expr source image", provenance := "ICCKernel.Raise.raiseTerm" }

theorem raiseSlice_lowerSlice (s : Substring) :
    raiseSlice (Lower.lowerSlice s) = s := by
  cases s
  rfl

theorem raiseSourceInfo_lowerSourceInfo (info : Lean.SourceInfo) :
    raiseSourceInfo (Lower.lowerSourceInfo info) = info := by
  cases info <;> simp [Lower.lowerSourceInfo, raiseSourceInfo, raiseSlice_lowerSlice]

theorem raisePreresolved_lowerPreresolved (p : Lean.Syntax.Preresolved) :
    raisePreresolved (Lower.lowerPreresolved p) = p := by
  cases p <;> simp [Lower.lowerPreresolved, raisePreresolved, raiseName_lowerName]

theorem raisePreresolvedList_lowerPreresolvedList : ∀ xs : List Lean.Syntax.Preresolved,
    List.map (raisePreresolved ∘ Lower.lowerPreresolved) xs = xs
  | [] => by
      rfl
  | x :: xs => by
      simp [raisePreresolved_lowerPreresolved, raisePreresolvedList_lowerPreresolvedList xs]

mutual

theorem raiseSyntax_lowerSyntax : ∀ stx : Lean.Syntax,
    raiseSyntax (Lower.lowerSyntax stx) = stx
  | .missing => by
      unfold Lower.lowerSyntax raiseSyntax
      rfl
  | .node info kind args => by
      unfold Lower.lowerSyntax raiseSyntax
      simp [raiseSourceInfo_lowerSourceInfo, raiseName_lowerName, raiseSyntaxList_lowerSyntaxList]
  | .atom info val => by
      unfold Lower.lowerSyntax raiseSyntax
      simp [raiseSourceInfo_lowerSourceInfo]
  | .ident info rawVal val preresolved => by
      unfold Lower.lowerSyntax raiseSyntax
      simp [raiseSourceInfo_lowerSourceInfo, raiseSlice_lowerSlice, raiseName_lowerName]
      exact raisePreresolvedList_lowerPreresolvedList preresolved

theorem raiseSyntaxList_lowerSyntaxList : ∀ xs : List Lean.Syntax,
    List.map raiseSyntax (Lower.lowerSyntaxList xs) = xs
  | [] => by
      rfl
  | x :: xs => by
      simp [Lower.lowerSyntaxList, raiseSyntax_lowerSyntax x, raiseSyntaxList_lowerSyntaxList xs]

end

theorem raiseMetaValue_lowerMetaValue (v : Lean.DataValue) :
    raiseMetaValue (Lower.lowerMetaValue v) = v := by
  cases v <;> simp [Lower.lowerMetaValue, raiseMetaValue, raiseName_lowerName, raiseSyntax_lowerSyntax]

theorem raiseLevelList_lowerLevelList : ∀ xs : List Lean.Level,
    List.map (raiseLevel ∘ Lower.lowerLevel) xs = xs
  | [] => by
      rfl
  | x :: xs => by
      simp [raiseLevel_lowerLevel, raiseLevelList_lowerLevelList xs]

theorem raiseMDataEntries_lowerEntries :
    ∀ xs : List (Lean.Name × Lean.DataValue),
      List.map (fun x => (raiseName (Lower.lowerName x.1), raiseMetaValue (Lower.lowerMetaValue x.2))) xs = xs
  | [] => by
      rfl
  | (key, value) :: xs => by
      simp [raiseName_lowerName, raiseMetaValue_lowerMetaValue]

theorem raiseMData_lowerMData (m : Lean.MData) :
    raiseMData (Lower.lowerMData m) = m := by
  cases m
  rename_i entries
  simpa [Lower.lowerMData, raiseMData] using raiseMDataEntries_lowerEntries entries

theorem raiseTerm_lowerExprCore (e : Lean.Expr) :
    raiseTerm (Lower.lowerExprCore e) = .ok e := by
  induction e with
  | bvar idx =>
      unfold Lower.lowerExprCore raiseTerm
      rfl
  | fvar id =>
      cases id
      unfold Lower.lowerExprCore raiseTerm
      simp [raiseName_lowerName]
  | mvar id =>
      cases id
      unfold Lower.lowerExprCore raiseTerm
      simp [raiseName_lowerName]
  | sort u =>
      unfold Lower.lowerExprCore raiseTerm
      simp [raiseLevel_lowerLevel]
  | const n us =>
      unfold Lower.lowerExprCore raiseTerm
      simp [raiseName_lowerName]
      exact raiseLevelList_lowerLevelList us
  | app f a ihf iha =>
      unfold Lower.lowerExprCore raiseTerm
      rw [ihf, iha]
      rfl
  | lam n ty body bi ihty ihbody =>
      unfold Lower.lowerExprCore raiseTerm
      rw [ihty, ihbody]
      simp [raiseName_lowerName, raiseBinderInfo_lowerBinderInfo]
      rfl
  | forallE n ty body bi ihty ihbody =>
      unfold Lower.lowerExprCore raiseTerm
      rw [ihty, ihbody]
      simp [raiseName_lowerName, raiseBinderInfo_lowerBinderInfo]
      rfl
  | letE n ty val body nonDep ihty ihval ihbody =>
      unfold Lower.lowerExprCore raiseTerm
      rw [ihty, ihval, ihbody]
      simp [raiseName_lowerName]
      rfl
  | lit value =>
      unfold Lower.lowerExprCore raiseTerm
      simp [raiseLiteral_lowerLiteral]
  | mdata data body ihbody =>
      unfold Lower.lowerExprCore raiseTerm
      rw [ihbody]
      simp [raiseMData_lowerMData]
      rfl
  | proj s idx body ihbody =>
      unfold Lower.lowerExprCore raiseTerm
      rw [ihbody]
      simp [raiseName_lowerName]
      rfl

end Raise
end ICCKernel
end LoF
end HeytingLean
