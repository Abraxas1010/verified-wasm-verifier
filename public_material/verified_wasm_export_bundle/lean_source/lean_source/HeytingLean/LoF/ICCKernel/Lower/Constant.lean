import Lean
import HeytingLean.LoF.ICCKernel.Lower.Expr

namespace HeytingLean
namespace LoF
namespace ICCKernel
namespace Lower

def lowerReducibilityHints : Lean.ReducibilityHints → ReducibilityHints
  | .opaque => .opaque
  | .abbrev => .abbrev
  | .regular h => .regular h.toNat

def lowerDefinitionSafety : Lean.DefinitionSafety → DefinitionSafety
  | .unsafe => .unsafe
  | .safe => .safe
  | .partial => .partial

def lowerQuotKind : Lean.QuotKind → QuotKind
  | .type => .type
  | .ctor => .ctor
  | .lift => .lift
  | .ind => .ind

def lowerConstHeader (v : Lean.ConstantVal) : ConstantVal :=
  { name := lowerName v.name
    levelParams := v.levelParams.map lowerName
    type := lowerExprCore v.type }

def lowerRecursorRule (r : Lean.RecursorRule) : RecursorRule :=
  { ctor := lowerName r.ctor, nfields := r.nfields, rhs := lowerExprCore r.rhs }

def lowerConstantInfoCore : Lean.ConstantInfo → ConstantInfo
  | .axiomInfo v =>
      .axiomInfo { (lowerConstHeader v.toConstantVal) with isUnsafe := v.isUnsafe }
  | .defnInfo v =>
      .defnInfo
        { (lowerConstHeader v.toConstantVal) with
          value := lowerExprCore v.value
          hints := lowerReducibilityHints v.hints
          safety := lowerDefinitionSafety v.safety
          all := v.all.map lowerName }
  | .thmInfo v =>
      .thmInfo { (lowerConstHeader v.toConstantVal) with value := lowerExprCore v.value, all := v.all.map lowerName }
  | .opaqueInfo v =>
      .opaqueInfo
        { (lowerConstHeader v.toConstantVal) with
          value := lowerExprCore v.value
          isUnsafe := v.isUnsafe
          all := v.all.map lowerName }
  | .quotInfo v =>
      .quotInfo { (lowerConstHeader v.toConstantVal) with kind := lowerQuotKind v.kind }
  | .inductInfo v =>
      .inductInfo
        { (lowerConstHeader v.toConstantVal) with
          numParams := v.numParams
          numIndices := v.numIndices
          all := v.all.map lowerName
          ctors := v.ctors.map lowerName
          numNested := v.numNested
          isRec := v.isRec
          isUnsafe := v.isUnsafe
          isReflexive := v.isReflexive }
  | .ctorInfo v =>
      .ctorInfo
        { (lowerConstHeader v.toConstantVal) with
          induct := lowerName v.induct
          cidx := v.cidx
          numParams := v.numParams
          numFields := v.numFields
          isUnsafe := v.isUnsafe }
  | .recInfo v =>
      .recInfo
        { (lowerConstHeader v.toConstantVal) with
          all := v.all.map lowerName
          numParams := v.numParams
          numIndices := v.numIndices
          numMotives := v.numMotives
          numMinors := v.numMinors
          rules := v.rules.map lowerRecursorRule
          k := v.k
          isUnsafe := v.isUnsafe }

def lowerConstantInfo (c : Lean.ConstantInfo) : Except LowerError ConstantInfo :=
  .ok (lowerConstantInfoCore c)

theorem lowerConstantInfo_noFallback : NoConstantFallback lowerConstantInfo := by
  intro c t h
  cases h
  cases c <;> simp [lowerConstantInfoCore, ConstantInfo.valueTerm?, Term.containsFallbackMarker]

theorem lowerConstantInfo_total (c : Lean.ConstantInfo) : ∃ t, lowerConstantInfo c = .ok t := by
  exact ⟨lowerConstantInfoCore c, by simp [lowerConstantInfo]⟩

end Lower
end ICCKernel
end LoF
end HeytingLean
