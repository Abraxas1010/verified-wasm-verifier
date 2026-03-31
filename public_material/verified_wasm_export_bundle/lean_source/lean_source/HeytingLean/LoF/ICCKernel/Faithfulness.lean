import HeytingLean.LoF.ICCKernel.Corpus
import HeytingLean.LoF.ICCKernel.Raise.Constant

namespace HeytingLean
namespace LoF
namespace ICCKernel

open Lower

def InLowerExprImage (e : Lean.Expr) : Prop :=
  ∃ t, Raise.raiseTerm t = .ok e

def InLowerConstantInfoImage (c : Lean.ConstantInfo) : Prop :=
  ∃ t, Raise.raiseConstantInfo t = .ok c

def recoverAndRelowerExpr (t : Term) : Except LowerError Term := do
  let e ← Raise.raiseTerm t
  Lower.lowerExpr e

def recoverAndRelowerConstantInfo (t : ConstantInfo) : Except LowerError ConstantInfo := do
  let c ← Raise.raiseConstantInfo t
  Lower.lowerConstantInfo c

def recoverAndRelowerExportedDecl (d : ExportedDecl) : Except LowerError ExportedDecl := do
  let c ← Raise.raiseConstantInfo d.decl
  let lowered ← Lower.lowerConstantInfo c
  pure { d with decl := lowered }

theorem lowerExpr_respects_noFallback :
    NoFallback lowerExpr :=
  lowerExpr_noFallback

theorem lowerConstantInfo_respects_noFallback :
    NoConstantFallback lowerConstantInfo :=
  lowerConstantInfo_noFallback

theorem lowerExpr_total_on_supported (e : Lean.Expr) :
    SupportedExpr e → ∃ t, lowerExpr e = .ok t := by
  intro _
  exact lowerExpr_total e

theorem lowerExpr_total_on_image (e : Lean.Expr) :
    InLowerExprImage e → ∃ t, lowerExpr e = .ok t := by
  intro _
  exact lowerExpr_total e

theorem lowerConstantInfo_total_on_supported (c : Lean.ConstantInfo) :
    SupportedConstantInfo c → ∃ t, lowerConstantInfo c = .ok t := by
  intro _
  exact lowerConstantInfo_total c

theorem lowerConstantInfo_total_on_image (c : Lean.ConstantInfo) :
    InLowerConstantInfoImage c → ∃ t, lowerConstantInfo c = .ok t := by
  intro _
  exact lowerConstantInfo_total c

theorem lowerExpr_output_has_no_fallback_marker (e : Lean.Expr) :
    ∀ t, lowerExpr e = .ok t → Term.containsFallbackMarker t = false := by
  intro t h
  exact lowerExpr_noFallback e t h

theorem raise_lowerExprCore_roundTrip (e : Lean.Expr) :
    Raise.raiseTerm (Lower.lowerExprCore e) = .ok e := by
  exact Raise.raiseTerm_lowerExprCore e

theorem recoverAndRelower_lowerExprCore_roundTrip (e : Lean.Expr) :
    recoverAndRelowerExpr (Lower.lowerExprCore e) = .ok (Lower.lowerExprCore e) := by
  rw [recoverAndRelowerExpr, raise_lowerExprCore_roundTrip]
  rfl

theorem lowerExpr_mem_image (e : Lean.Expr) :
    InLowerExprImage e := by
  exact ⟨Lower.lowerExprCore e, raise_lowerExprCore_roundTrip e⟩

theorem raise_lowerConstantInfo_roundTrip (c : Lean.ConstantInfo) :
    Raise.raiseConstantInfo (Lower.lowerConstantInfoCore c) = .ok c := by
  exact Raise.raiseConstantInfo_lowerConstantInfoCore c

theorem recoverAndRelower_lowerConstantInfoCore_roundTrip (c : Lean.ConstantInfo) :
    recoverAndRelowerConstantInfo (Lower.lowerConstantInfoCore c) = .ok (Lower.lowerConstantInfoCore c) := by
  rw [recoverAndRelowerConstantInfo, raise_lowerConstantInfo_roundTrip]
  rfl

theorem lowerConstantInfo_mem_image (c : Lean.ConstantInfo) :
    InLowerConstantInfoImage c := by
  exact ⟨Lower.lowerConstantInfoCore c, raise_lowerConstantInfo_roundTrip c⟩

theorem lowerExprCore_injective {e₁ e₂ : Lean.Expr}
    (h : Lower.lowerExprCore e₁ = Lower.lowerExprCore e₂) : e₁ = e₂ := by
  have h₁ := Raise.raiseTerm_lowerExprCore e₁
  have h₂ := Raise.raiseTerm_lowerExprCore e₂
  rw [h] at h₁
  exact Except.ok.inj (h₁.symm.trans h₂)

theorem raiseLowerExpr_image_characterization (e : Lean.Expr) :
    Raise.raiseTerm (Lower.lowerExprCore e) = .ok e := by
  exact raise_lowerExprCore_roundTrip e

theorem raiseLowerConstantInfo_image_characterization (c : Lean.ConstantInfo) :
    Raise.raiseConstantInfo (Lower.lowerConstantInfoCore c) = .ok c := by
  exact raise_lowerConstantInfo_roundTrip c

theorem raiseConstantInfoList_lowerConstantInfoList : ∀ xs : List Lean.ConstantInfo,
    List.mapM (fun c => Raise.raiseConstantInfo (Lower.lowerConstantInfoCore c)) xs = .ok xs
  | [] => by
      rfl
  | x :: xs => by
      simp [raise_lowerConstantInfo_roundTrip x, raiseConstantInfoList_lowerConstantInfoList xs]
      simpa using Raise.exceptOk_bind_map_eq List.cons x xs

theorem lowerConstantInfoList_roundTrip : ∀ xs : List Lean.ConstantInfo,
    List.mapM Lower.lowerConstantInfo xs = .ok (xs.map Lower.lowerConstantInfoCore)
  | [] => by
      rfl
  | x :: xs => by
      simp [Lower.lowerConstantInfo, lowerConstantInfoList_roundTrip xs]
      simpa using
        Raise.exceptOk_bind_map_eq List.cons (Lower.lowerConstantInfoCore x) (List.map Lower.lowerConstantInfoCore xs)

def lowerModuleBundleCore (moduleName : Lean.Name) (constants : List Lean.ConstantInfo) : ModuleBundle :=
  { moduleName := Lower.lowerName moduleName
    constants := constants.map Lower.lowerConstantInfoCore }

def raiseModuleBundle (bundle : ModuleBundle) : Except LowerError (Lean.Name × List Lean.ConstantInfo) := do
  let constants ← bundle.constants.mapM Raise.raiseConstantInfo
  pure (Raise.raiseName bundle.moduleName, constants)

def recoverAndRelowerModuleBundle (bundle : ModuleBundle) : Except LowerError ModuleBundle := do
  let (_, constants) ← raiseModuleBundle bundle
  let lowered ← constants.mapM Lower.lowerConstantInfo
  pure { bundle with constants := lowered }

theorem raise_lowerModuleBundleCore_roundTrip (moduleName : Lean.Name) (constants : List Lean.ConstantInfo) :
    raiseModuleBundle (lowerModuleBundleCore moduleName constants) = .ok (moduleName, constants) := by
  simp [raiseModuleBundle, lowerModuleBundleCore, Raise.raiseName_lowerName]
  have hconsts : List.mapM (Raise.raiseConstantInfo ∘ lowerConstantInfoCore) constants = .ok constants := by
    simpa [Function.comp] using raiseConstantInfoList_lowerConstantInfoList constants
  rw [hconsts]
  simpa using Raise.exceptOk_map_eq (Prod.mk moduleName) constants

theorem recoverAndRelower_loweredExportedDecl_roundTrip
    (moduleName : Lean.Name) (c : Lean.ConstantInfo) :
    recoverAndRelowerExportedDecl
      { moduleName := Lower.lowerName moduleName, decl := Lower.lowerConstantInfoCore c } =
      .ok { moduleName := Lower.lowerName moduleName, decl := Lower.lowerConstantInfoCore c } := by
  rw [recoverAndRelowerExportedDecl, raise_lowerConstantInfo_roundTrip]
  rfl

theorem lowerConstantInfoCore_injective {c₁ c₂ : Lean.ConstantInfo}
    (h : Lower.lowerConstantInfoCore c₁ = Lower.lowerConstantInfoCore c₂) : c₁ = c₂ := by
  have h₁ := Raise.raiseConstantInfo_lowerConstantInfoCore c₁
  have h₂ := Raise.raiseConstantInfo_lowerConstantInfoCore c₂
  rw [h] at h₁
  exact Except.ok.inj (h₁.symm.trans h₂)

end ICCKernel
end LoF
end HeytingLean
